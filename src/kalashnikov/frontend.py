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
    if is_nested_loop(ast):
      print "ERROR: nested loop"
      sys.exit(10)

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

def split_func(fd, ofile):
  prog = FlatProgram()

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

  ofile.write('#include "synth.h"\n')
  ofile.write("/*\n")

  for id in sorted(rev_id_map.keys()):
    ofile.write(" * %s -> %d\n" % (rev_id_map[id], id))

  ofile.write("*/\n\n");

  nids = len(id_map)

  prefix = copy.deepcopy(prog.blocks[0])
  loop = copy.deepcopy(prog.blocks[1])

  #(prefix, prefix_nondet) = replace_nondet(prefix)
  #(guard, guard_nondet) = replace_nondet(loop.cond)
  #(body, body_nondet) = replace_nondet(loop.stmt)

  decls = []
  copy_out = []

  retvis = ReturnVisitor()
  retvis.visit(prefix)

  for b in prefix.block_items:
    if isinstance(b, c_ast.Decl):
      id = b.name
      vid = id_map[id]

      b.init = c_ast.ArrayRef(c_ast.ID('in_vars'),
                              c_ast.Constant('int', str(vid)))

      decls.append(b)

  for id in sorted(rev_id_map.keys()):
    varname = rev_id_map[id]
    arr = c_ast.ArrayRef(c_ast.ID('out_vars'),
                         c_ast.Constant('int', str(id)))
    var = c_ast.ID(varname)

    copy_out.append(c_ast.Assignment("=", arr, var))


  prefix.block_items += copy_out
  prefix.block_items.append(c_ast.Return(c_ast.Constant('int', str('1'))))

  ofile.write("int prefix(word_t in_vars[%d], word_t out_vars[%d]) {\n" % (nids, nids))
  ofile.write(cgen.visit(prefix))
  ofile.write("}\n\n")

  ofile.write("int guard(word_t in_vars[%d]) {\n" % nids)
  guard_body = c_ast.Compound(copy.copy(decls))
  guard_body.block_items.append(c_ast.Return(loop.cond))
  ofile.write(cgen.visit(guard_body))
  ofile.write("}\n\n")

  ofile.write("void body(word_t in_vars[%d], word_t out_vars[%d]) {\n" % (nids, nids))
  loop_body = c_ast.Compound(copy.copy(decls))
  loop_body.block_items.append(loop.stmt)
  loop_body.block_items += copy_out
  ofile.write(cgen.visit(loop_body))
  ofile.write("}\n\n")

  return rev_id_map


def split(filename, ofile=sys.stdout):
  ast = parse_file_libc(filename)
  prog = FlatProgram()

  for fd in ast.ext:
    if not isinstance(fd, c_ast.FuncDef):
      continue

    if not fd.decl.name == 'main':
      continue

    return split_func(fd, ofile)

def prove_terminates(filename):
  splitfile = tempfile.NamedTemporaryFile(mode='w', suffix='.c', delete=False)
  id_map = split(filename, splitfile)
  nids = len(id_map)
  varnames = ' '.join(id_map[k] for k in xrange(nids))

  splitfile.close()

  return os.system(("./kalashnikov.py " +
             "%s ../../papers/termination/experiments/benchmarks/ranking.c " +
             "-s2 --seed=1337 -w4 -a%d --varnames %s --resnames I " +
             "%s") % 
              (splitfile.name,
                nids,
                varnames,
                ' '.join(sys.argv[2:])))

if __name__ == '__main__':
  import sys

  try:
    os.unlink("/tmp/geneticsynth")
  except:
    pass

  try:
    os.unlink("/tmp/annealsynth")
  except:
    pass

  sys.exit(prove_terminates(sys.argv[1]))
