#!/usr/bin/python

import os
import sys
import copy

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

def split(filename):
  ast = parse_file_libc(filename)
  prog = FlatProgram()

  for fd in ast.ext:
    if not isinstance(fd, c_ast.FuncDef):
      continue

    print "Flattening %s" % fd.decl.name

    flatten(fd.body, prog)
    cgen = c_generator.CGenerator()

    for b in prog.blocks:
      if is_loop(b):
        print "Loop:"
        print cgen.visit(b)
      else:
        print "Straight line:"
        print cgen.visit(b)

if __name__ == '__main__':
  import sys

  split(sys.argv[1])
