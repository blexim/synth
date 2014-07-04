#!/usr/bin/python

import os
import sys
import copy
import tempfile

sys.path.extend(["pycparser"])

from pycparser import parse_file, c_generator, c_ast

def parse_file_libc(filename):
  return parse_file(filename, use_cpp=True,
      cpp_args="-Ipycparser/utils/fake_libc_include")

class DeclVisitor(c_ast.NodeVisitor):
  def __init__(self):
    self.ids = {}
    self.revids = {}

  def visit_Decl(self, decl):
    if not isinstance(decl.type, c_ast.TypeDecl):
      return

    if decl.name not in self.ids:
      n = len(self.ids)
      self.ids[decl.name] = n
      self.revids[n] = decl.name

def number_ids(ast):
  v = DeclVisitor()
  v.visit(ast)

  return (v.ids, v.revids)

def is_loop(ast):
  return (isinstance(ast, c_ast.DoWhile) or
      isinstance(ast, c_ast.While) or
      isinstance(ast, c_ast.For))

loop_memo = {}

def contains_loop(ast):
  if ast in loop_memo:
    return loop_memo[ast]

  ret = False

  if is_loop(ast):
    ret = True
  else:
    for (_, c) in ast.children():
      if contains_loop(c):
        ret = True
        break

  loop_memo[ast] = ret

  return ret

def is_nested_loop(ast):
  if is_loop(ast):
    return contains_loop(ast.stmt)

  return False

def add_parents(ast):
  if getattr(ast, 'parent', None) is None:
    ast.parent = None

  for c in ast.children():
    c[1].parent = ast
    add_parents(c[1])

class FlatProgram(object):
  def __init__(self):
    self.blocks = []
    self.start_straightline()

  def start_straightline(self):
    self.curr = []
    compound = c_ast.Compound(self.curr)
    self.blocks.append(compound)

  def accumulate(self, ast):
    if is_loop(ast):
      self.blocks.append(ast)
      self.start_straightline()
    elif isinstance(ast, c_ast.Compound):
      self.curr += ast.block_items
    else:
      self.curr.append(ast)

def flatten(ast, program):
  if not contains_loop(ast):
    program.accumulate(ast)
  elif is_loop(ast):
    program.accumulate(ast)
  else:
    # The AST contains a loop.  Recurse on its children.
    for (_, c) in ast.children():
      flatten(c, program)

class ReturnVisitor(c_ast.NodeVisitor):
  def visit_Return(self, node):
    node.expr = c_ast.Constant('int', '0')

def is_nondet(ast):
  return isinstance(ast, c_ast.FuncCall) and ast.name.name == 'nondet'

def replace_nondet(ast, nondet_idx=0):
  if is_nondet(ast):
    return (c_ast.ID('nondet_%d' % nondet_idx), nondet_idx + 1)
  elif isinstance(ast, list):
    ret = []

    for x in ast:
      (x_, nondet_idx) = replace_nondet(x, nondet_idx)
      ret.append(x_)

    return (ret, nondet_idx)
  elif isinstance(ast, c_ast.Node):
    ret = copy.copy(ast)

    for (k, v) in ast.__dict__.items():
      (v_, nondet_idx) = replace_nondet(v, nondet_idx)
      ret.__dict__[k] = v_

    return (ret, nondet_idx)
  else:
    return (ast, nondet_idx)

def is_signed(decl):
  return decl.type.type.names in (['int'], ['long'])

class FileWriter(object):
  def __init__(self, ofile, cgen):
    self.ofile = ofile
    self.cgen = cgen

  def write(self, ast):
    if isinstance(ast, list):
      for a in ast:
        self.write_c(self, a)
    elif isinstance(ast, c_ast.Node):
      self.ofile.write(self.cgen.visit(ast))
    else:
      self.ofile.write(str(ast))

def split_func(fd, ofile):
  prog = FlatProgram()
  has_nested = False

  (fd, nondet) = replace_nondet(fd)
  fd_body = fd.body

  for i in xrange(nondet):
    id = c_ast.ID('nondet_%d' % i)

    decl = c_ast.Decl(id.name,
                      [],
                      [],
                      [],
                      c_ast.TypeDecl(id.name, [], c_ast.IdentifierType(['word_t'])),
                      None,
                      None)

    fd_body.block_items.insert(0, decl)

  flatten(fd_body, prog)
  cgen = c_generator.CGenerator()
  (id_map, rev_id_map) = number_ids(fd)
  f = FileWriter(ofile, cgen)

  f.write('#include "synth.h"\n')
  f.write("/*\n")

  for id in sorted(rev_id_map.keys()):
    f.write(" * %s -> %d\n" % (rev_id_map[id], id))

  f.write("*/\n\n");

  nids = len(id_map)

  prefix = copy.deepcopy(prog.blocks[0])
  loop = copy.deepcopy(prog.blocks[1])

  #(prefix, prefix_nondet) = replace_nondet(prefix)
  #(guard, guard_nondet) = replace_nondet(loop.cond)
  #(body, body_nondet) = replace_nondet(loop.stmt)

  decls = []
  copy_out = []
  prefix_block = []

  retvis = ReturnVisitor()
  retvis.visit(prefix)

  for b in prefix.block_items:
    prefix_block.append(b)

    if isinstance(b, c_ast.Decl):
      id = b.name
      vid = id_map[id]

      b.init = c_ast.ArrayRef(c_ast.ID('in_vars'),
                              c_ast.Constant('int', str(vid)))

      decls.append(b)

      if is_signed(b):
        extend = c_ast.FuncCall(c_ast.ID('SIGN_EXTEND'),
                                c_ast.ExprList([c_ast.ID(id)]))
        decls.append(extend)
        prefix_block.append(extend)

  prefix.block_items = prefix_block

  for id in sorted(rev_id_map.keys()):
    varname = rev_id_map[id]
    arr = c_ast.ArrayRef(c_ast.ID('out_vars'),
                         c_ast.Constant('int', str(id)))
    var = c_ast.ID(varname)

    copy_out.append(c_ast.Assignment("=", arr, var))

  copy_out.append(c_ast.Return(c_ast.Constant('int', str('1'))))

  prefix.block_items += copy_out

  f.write("int prefix(word_t in_vars[NARGS], word_t out_vars[NARGS]) {\n")
  f.write(prefix)
  f.write("}\n\n")

  f.write("int guard(word_t in_vars[NARGS]) {\n")
  guard_body = c_ast.Compound(copy.copy(decls))
  guard_body.block_items.append(c_ast.Return(loop.cond))
  f.write(guard_body)
  ofile.write("}\n\n")

  if is_nested_loop(loop):
    has_nested = True

    nested_prog = FlatProgram()
    flatten(loop.stmt, nested_prog)
    inner_prefix = nested_prog.blocks[0]
    inner_body = nested_prog.blocks[1]
    inner_suffix = nested_prog.blocks[2]

    inner_guard = c_ast.Compound(copy.copy(decls) + [c_ast.Return(inner_body.cond)])

    if isinstance(inner_body.stmt, c_ast.Compound):
      inner_body = inner_body.stmt.block_items
    else:
      inner_body = [inner_body.stmt]

    inner_body = c_ast.Compound(copy.copy(decls) + inner_body + copy_out)
    outer_guard = c_ast.Compound(copy.copy(decls) + [c_ast.Return(loop.cond)])

    f.write("int inner_prefix(word_t in_vars[NARGS], word_t out_vars[NARGS]) {\n")
    inner_prefix.block_items = decls + inner_prefix.block_items + copy_out
    f.write(inner_prefix)
    f.write("}\n\n")

    f.write("int inner_guard(word_t in_vars[NARGS]) {\n")
    f.write(inner_guard)
    f.write("}\n\n")

    f.write("int inner_body(word_t in_vars[NARGS], word_t out_vars[NARGS]) {\n")
    f.write(inner_body)
    f.write("}\n\n")

    f.write("int inner_suffix(word_t in_vars[NARGS], word_t out_vars[NARGS]) {\n")
    inner_suffix.block_items = decls + inner_suffix.block_items + copy_out
    f.write(inner_suffix)
    f.write("}\n\n")

    f.write("int outer_guard(word_t in_vars[NARGS]) {\n")
    f.write(outer_guard)
    f.write("}\n\n")
  else:
    f.write("void body(word_t in_vars[NARGS], word_t out_vars[NARGS]) {\n")
    loop_body = c_ast.Compound(copy.copy(decls) + loop.stmt.block_items + copy_out)
    f.write(loop_body)
    f.write("}\n\n")

  return (rev_id_map, has_nested)

def split(filename, ofile=sys.stdout):
  ast = parse_file_libc(filename)
  prog = FlatProgram()

  for fd in ast.ext:
    if not isinstance(fd, c_ast.FuncDef):
      continue

    if not fd.decl.name == 'main':
      continue

    return split_func(fd, ofile)

if __name__ == '__main__':
  import sys

  split(sys.argv[1])
