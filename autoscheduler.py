#!/usr/bin/env python

import itertools
import random
import z3

### utils

def flatten(lst):
  return [item for elem in lst for item in elem]

solver = z3.Solver()

### data types for schedule and expressions

# schedule data types

SENTRY  = -1
ROOT    = 0 
LOOP    = 1
COMPUTE = 2
STORAGE = 3


# loop types

SEQUENTIAL = 1
PARALLEL   = 2
VECTORIZED = 3
UNROLLED   = 4


# dimensions

X_VAR       = "x"
X_INNER_VAR = "x_inner"
X_OUTER_VAR = "x_outer"

Y_VAR       = "y"
Y_INNER_VAR = "y_inner"
Y_OUTER_VAR = "y_outer"

XY_VAR      = "xy"

SPLIT_FACTORS = [2, 4, 8, 16, 32, 64, 128]
VECTOR_SIZES  = [2, 4, 8]


# smart constructors

def sentry():
  return { "type": SENTRY }


def root(children):
  return {
    "type": ROOT,
    "children": children
  }


def loop(func, v, loop_type, children, size=None):
  return {
    "type": LOOP,
    "func": func,
    "var": v,
    "loop_type": loop_type,
    "size": size if size is not None else var((func, v)),
    "children": children
  }


def storage(func, children):
  return {
    "type": STORAGE,
    "func": func,
    "size": times(var((func,X_VAR)), var((func,Y_VAR))),
    "children": children
  }


def compute(func, children):
  for child in children:
    if "type" not in child or child["type"] != COMPUTE:
      raise Exception("compute node can only have other compute nodes as children")

  return {
    "type": COMPUTE,
    "func": func,
    "children": children
  }


# function def data types

FUNC    = 0
VAR     = 1
CONST   = 2
OP      = 3


# operations

PLUS    = 0
MINUS   = 1
TIMES   = 2
DIVIDE  = 3
SIN     = 4
COS     = 5
TAN     = 6
SQRT    = 7

# smart constructors

def func(f, x, y):
  return {
    "type": FUNC,
    "func": f,
    "x": x,
    "y": y
  }

def x():
  return {
    "type": VAR,
    "var": X_VAR
  }

def y():
  return {
    "type": VAR,
    "var": Y_VAR
  }

def var(v):
  return {
    "type": VAR,
    "var": v
  }

def const(n):
  return {
    "type": CONST,
    "val": n
  }

def op(operation, operands):
  return {
    "type": OP,
    "op": operation,
    "operands": operands
  }

def plus(lhs, rhs):
  return op(PLUS, [lhs, rhs])

def minus(lhs, rhs):
  return op(MINUS, [lhs, rhs])

def times(lhs, rhs):
  return op(TIMES, [lhs, rhs])

def divide(lhs, rhs):
  return op(DIVIDE, [lhs, rhs])

def sin(x):
  return op(SIN, [x])

def cos(x):
  return op(COS, [x])

def tan(x):
  return op(TAN, [x])

def sqrt(x):
  return op(SQRT, [x])

# datatype utils

def eval_expr(env, expr):
  if expr["type"] == VAR and expr["var"] in env:
    return env[expr["var"]]

  elif expr["type"] == VAR and expr["var"] not in env:
    raise Exception("eval_expr: var " + str(expr["var"]) + " not found in environment")

  elif expr["type"] == CONST:
    return expr["val"]

  elif expr["type"] == OP:
    if expr["op"] == PLUS:
      val_lhs = eval_expr(env, expr["operands"][0])
      val_rhs = eval_expr(env, expr["operands"][1])
      return val_lhs + val_rhs

    if expr["op"] == MINUS:
      val_lhs = eval_expr(env, expr["operands"][0])
      val_rhs = eval_expr(env, expr["operands"][1])
      return val_lhs - val_rhs

    if expr["op"] == TIMES:
      val_lhs = eval_expr(env, expr["operands"][0])
      val_rhs = eval_expr(env, expr["operands"][1])
      return val_lhs * val_rhs

    if expr["op"] == DIVIDE:
      val_lhs = eval_expr(env, expr["operands"][0])
      val_rhs = eval_expr(env, expr["operands"][1])
      return val_lhs / val_rhs

    else:
      raise Exception("operand " + expr["op"] + " not supported")

  else:
    raise Exception("expression type " + str(expr) + " not supported")


def print_expr(expr):
  if expr["type"] == VAR:
    return expr["var"]

  elif expr["type"] == CONST:
    return str(expr["val"])

  elif expr["type"] == FUNC:
    val_x = print_expr(expr["x"])
    val_y = print_expr(expr["y"])
    return "{}({},{})".format(expr["func"], val_x, val_y)

  elif expr["type"] == OP:
    if expr["op"] == PLUS:
      val_lhs = print_expr(expr["operands"][0])
      val_rhs = print_expr(expr["operands"][1])
      return "{} + {}".format(val_lhs, val_rhs)

    elif expr["op"] == MINUS:
      val_lhs = print_expr(expr["operands"][0])
      val_rhs = print_expr(expr["operands"][1])
      return "{} - {}".format(val_lhs, val_rhs)

    elif expr["op"] == TIMES:
      val_lhs = print_expr(expr["operands"][0])
      val_rhs = print_expr(expr["operands"][1])
      return "{} * {}".format(val_lhs, val_rhs)

    elif expr["op"] == DIVIDE:
      val_lhs = print_expr(expr["operands"][0])
      val_rhs = print_expr(expr["operands"][1])
      return "{} / {}".format(val_lhs, val_rhs)

    elif expr["op"] == SIN:
      val = print_expr(expr["operands"][0])
      return "sin({})".format(val)

    elif expr["op"] == COS:
      val = print_expr(expr["operands"][0])
      return "cos({})".format(val)

    elif expr["op"] == TAN:
      val = print_expr(expr["operands"][0])
      return "cos({})".format(val)

    elif expr["op"] == SQRT:
      val = print_expr(expr["operands"][0])
      return "sqrt({})".format(val)


# get ancestry paths for compute nodes
def get_ancestor_map(schedule):
  ancestor_map = {}
  ancestors = []
  visit_list = [schedule]
  while len(visit_list) > 0:
    node = visit_list.pop()

    if node["type"] == SENTRY:
      ancestors.pop()

    elif node["type"] in [ROOT, LOOP, STORAGE]:
      visit_list.append(sentry())
      visit_list.extend(list(reversed(node["children"])))
      ancestors.append(node)

    elif node["type"] == COMPUTE:
      ancestor_map[node["func"]] = list(ancestors)

  return ancestor_map



def get_calls(expr, f):
  if expr["type"] == FUNC:
    if expr["func"] == f:
      return [expr]

  elif expr["type"] == VAR:
    return []

  elif expr["type"] == CONST:
    return []

  elif expr["type"] == OP:
    return flatten(map(lambda o: get_calls(o, f), expr["operands"]))


def print_schedule(schedule, indent=0):
  if schedule["type"] == ROOT:
    print (" " * indent),
    print "root"
    map(lambda c: print_schedule(c, indent+2), schedule["children"])

  elif schedule["type"] == LOOP:
    print (" " * indent),
    print "loop", schedule["func"], schedule["var"], schedule["loop_type"], schedule["size"]
    map(lambda c: print_schedule(c, indent+2), schedule["children"])

  elif schedule["type"] == STORAGE:
    print (" " * indent),
    print "storage", schedule["func"], schedule["size"]
    map(lambda c: print_schedule(c, indent+2), schedule["children"])

  elif schedule["type"] == COMPUTE:
    print (" " * indent),
    print "compute", schedule["func"]
    map(lambda c: print_schedule(c, indent+2), schedule["children"])


def copy_expr(expr):
  if expr["type"] == FUNC:
    return func(expr["func"], copy_expr(expr["x"]), copy_expr(expr["y"]))

  elif expr["type"] == VAR:
    return var(expr["var"])

  elif expr["type"] == CONST:
    return const(expr["val"])

  elif expr["type"] == OP:
    return op(expr["op"], map(copy_expr, expr["operands"]))

def copy_schedule(schedule):
  if schedule["type"] == ROOT:
    return root(map(copy_schedule, schedule["children"]))

  elif schedule["type"] == LOOP:
    size = schedule["size"]
    if type(schedule["size"]) != int:
      size = copy_expr(schedule["size"])

    return loop(schedule["func"], schedule["var"], schedule["loop_type"], \
              map(copy_schedule, schedule["children"]), size)

  elif schedule["type"] == STORAGE:
    return storage(schedule["func"], map(copy_schedule, schedule["children"]))

  elif schedule["type"] == COMPUTE:
    return compute(schedule["func"], map(copy_schedule, schedule["children"]))


# get the functions that call this function
def get_callers(func_info, func):
  callers = []
  for f in func_info:
    if func in get_callees(func_info, f):
      callers.append(f)

  return callers


# get the functions that this function calls
def get_callees(func_info, func):
  funcs = set()
  node_list = [func_info[func]]

  while len(node_list) > 0:
    node = node_list.pop()

    if node["type"] == FUNC:
      funcs.add(node["func"])

    elif node["type"] == VAR:
      pass

    elif node["type"] == CONST:
      pass

    elif node["type"] == OP:
      node_list.extend(node["operands"])

  return funcs


def get_descendants(node):
  visit_list = [node]
  children = []

  while len(visit_list) > 0:
    node = visit_list.pop()
    children.append(node)

    if node["type"] == ROOT:
      visit_list += list(reversed(node["children"]))

    elif node["type"] == LOOP:
      visit_list += list(reversed(node["children"]))

    elif node["type"] == STORAGE:
      visit_list += list(reversed(node["children"]))

    elif node["type"] == COMPUTE:
      pass
      # visit_list += list(reversed(node["children"]))

  return children


# check two conditions:
# - compute node occurs before compute nodes of calling functions
#   in a depth-first traversal
# - storage node must be an ancestor of compute node and caller's compute nodes
def is_legal_schedule(func_info, schedule):
  visit_list = [schedule]
  ancestors = []
  compute_nodes_visited = []

  while len(visit_list) > 0:
    node = visit_list.pop()
    if node["type"] == SENTRY:
      ancestors.pop()

    elif node["type"] == ROOT:
      visit_list.append(sentry())
      visit_list.extend(list(reversed(node["children"])))
      ancestors.append(node)

    elif node["type"] == LOOP:
      # illegal: should only vectorize innermost loops
      if node["loop_type"] == VECTORIZED:
        child_loops = [child for child in get_descendants(node) if child["type"] == LOOP]
        if len(child_loops) > 0:
          # print "vectorizing loop that is not innermost"
          return False

      visit_list.append(sentry())
      visit_list.extend(list(reversed(node["children"])))
      ancestors.append(node)

    elif node["type"] == STORAGE:
      visit_list.append(sentry())
      visit_list.extend(list(reversed(node["children"])))
      ancestors.append(node)

    elif node["type"] == COMPUTE:
      func = node["func"]
      inlined_funcs = [inlinedf["func"] for inlinedf in node["children"]]
      called_funcs = get_callees(func_info, func)
      storage_ancestors = [a["func"] for a in ancestors if a["type"] == STORAGE]

      for f in called_funcs:
        # illegal: called function is neither inlined nor called!
        if f not in inlined_funcs and f not in compute_nodes_visited:
          # print "function not a storage ancestor"
          return False

        # illegal: storage must be an ancestor of called functions
        if f not in inlined_funcs and f not in storage_ancestors:
          # print "called function not a storage ancestor"
          return False

      compute_nodes_visited.append(node["func"])
      visit_list.append(sentry())
      visit_list.extend(list(reversed(node["children"])))
      ancestors.append(node)


  return True


def inline_all_callees(func_info, func):
  callees = get_callees(func_info, func)
  children = [inline_all_callees(func_info, child) for child in callees]
  return compute(func, children)


# get default schedule for output function,
# which inlines all called functions
def default_schedule(func_info, func):
  compute_f = inline_all_callees(func_info, func)
  loop_x = loop(func, X_VAR, SEQUENTIAL, [compute_f])
  loop_y = loop(func, Y_VAR, SEQUENTIAL, [loop_x])
  return root([loop_y])


### schedule transformers

def traverse_schedule(f):
  def wrapper(func_info, schedule):
    for fs in f(func_info, schedule):
      yield fs

    possible_children = map(lambda child: wrapper(func_info, child), schedule["children"])
    if len(possible_children) > 0:
      for children in (list(x) for x in itertools.product(*possible_children)):
        new_schedule = copy_schedule(schedule)
        new_schedule["children"] = children
        yield new_schedule

  return wrapper


def get_split_variable(var):
  if var == X_VAR:
    return [X_OUTER_VAR, X_INNER_VAR]
  
  elif var == Y_VAR:
    return [Y_OUTER_VAR, Y_INNER_VAR]

  else:
    return []


# constraint: only split one level to simplify search
@traverse_schedule
def split(func_info, schedule):
  if schedule["type"] == LOOP:
    new_loops = []

    split_vars = get_split_variable(schedule["var"])
    if len(split_vars) > 0:
      for split_factor in SPLIT_FACTORS:
        inner_loop = loop(schedule["func"], split_vars[1], \
            schedule["loop_type"], schedule["children"], const(split_factor))
        outer_loop = loop(schedule["func"], split_vars[0], \
            schedule["loop_type"], [inner_loop], divide(schedule["size"], const(split_factor)))

        yield outer_loop


def get_fuse_variable(var1, var2):
  if (var1 == X_VAR and var2 == Y_VAR) or (var1 == Y_VAR and var2 == X_VAR):
    return XY_VAR

  else:
    return None


@traverse_schedule
def fuse(func_info, schedule):
  return
  yield


@traverse_schedule
def reorder(func_info, schedule):
  if schedule["type"] == LOOP:
    children = schedule["children"]
    for i in range(len(children)):
      if children[i]["type"] == LOOP and schedule["func"] == children[i]["func"] \
          and not ((schedule["var"] == X_OUTER_VAR and children[i]["var"] == X_INNER_VAR) \
            or (schedule["var"] == Y_OUTER_VAR and children[i]["var"] == Y_INNER_VAR)):

        new_loop = copy_schedule(schedule)
        
        child_var = new_loop["children"][i]["var"]
        child_loop_type = new_loop["children"][i]["loop_type"]
        child_size = new_loop["children"][i]["size"]

        new_loop["children"][i]["var"] = new_loop["var"]
        new_loop["children"][i]["loop_type"] = new_loop["loop_type"]
        new_loop["children"][i]["size"] = new_loop["size"]

        new_loop["var"] = child_var
        new_loop["loop_type"] = child_loop_type
        new_loop["size"] = child_size

        yield new_loop


@traverse_schedule
def change_loop_type(func_info, schedule):
  if schedule["type"] == LOOP:
    new_loops = []

    loop_types = [SEQUENTIAL, VECTORIZED]
    for new_loop_type in filter(lambda x: x != schedule["loop_type"], loop_types):
      can_change = True
      if new_loop_type == VECTORIZED:
        if schedule["size"]["type"] != CONST \
            or schedule["size"]["val"] not in VECTOR_SIZES:
          can_change = False

      if can_change:
        new_loop = copy_schedule(schedule)
        new_loop["loop_type"] = new_loop_type
        yield new_loop


@traverse_schedule
def hoist_compute(func_info, schedule):
  if schedule["type"] in [ROOT, LOOP, STORAGE]:
    children = schedule["children"]
    for i in range(len(children)):
      if children[i]["type"] == LOOP:
        child = children[i]
        grandchildren = child["children"]
        for j in range(len(grandchildren)):
          if grandchildren[j]["type"] == LOOP and child["func"] != grandchildren[j]["func"]:
            new_child = copy_schedule(children[i])
            new_child["children"] = \
                children[i]["children"][:j] + children[i]["children"][j+1:]

            new_loop = copy_schedule(schedule)
            new_loop["children"] = \
                children[:i] + [grandchildren[j], new_child] + children[i+1:]

            yield new_loop


@traverse_schedule
def lower_compute(func_info, schedule):
  if schedule["type"] == LOOP:
    children = schedule["children"]
    for i in range(len(children)):
      for j in range(i+1, len(children)):
        if children[i]["type"] == LOOP and children[j]["type"] == LOOP \
            and children[i]["func"] != children[j]["func"]:

          new_child = copy_schedule(children[j])
          new_child["children"] = [children[i]] + new_child["children"]

          new_loop = copy_schedule(schedule)
          new_loop["children"][j] = new_child
          new_loop["children"] = new_loop["children"][:i] + new_loop["children"][i+1:]

          yield new_loop


@traverse_schedule
def hoist_storage(func_info, schedule):
  if schedule["type"] == LOOP:
    children = schedule["children"]
    for i in range(len(children)):
      if children[i]["type"] == STORAGE:
        new_loop = copy_schedule(schedule)
        new_loop["children"] = \
            schedule["children"][:i] + children[i]["children"] + schedule["children"][i+1:]

        new_storage = copy_schedule(children[i])
        new_storage["children"] = [new_loop]

        yield new_storage


@traverse_schedule
def lower_storage(func_info, schedule):
  pass


def remove_func(schedule, func):
  apply_to_children = lambda: \
      flatten(map(lambda child: remove_func(child, func), schedule["children"]))

  if schedule["type"] == ROOT:
    new_root = copy_schedule(schedule)
    new_root["children"] = apply_to_children()
    return [new_root]

  elif schedule["type"] == LOOP:
    if schedule["func"] == func:
      return apply_to_children()

    else:
      new_loop = copy_schedule(schedule)
      new_loop["children"] = apply_to_children()
      return [new_loop]

  elif schedule["type"] == STORAGE:
    if schedule["func"] == func:
      return apply_to_children()

    else:
      new_storage = copy_schedule(schedule)
      new_storage["children"] = apply_to_children()
      return [new_storage]

  elif schedule["type"] == COMPUTE:
    if schedule["func"] == func:
      return []

    else:
      new_compute = copy_schedule(schedule)
      return [new_compute]


def inline_func(schedule, func_info, func):
  if schedule["type"] == COMPUTE:
    if func in get_callees(func_info, schedule["func"]):
      new_compute = copy_schedule(schedule)
      new_compute["children"].append(compute(func,[]))
      return new_compute

    else:
      return copy_schedule(schedule)

  else:
    new_schedule = copy_schedule(schedule)
    new_schedule["children"] = \
        map(lambda child: inline_func(child, func_info, func), new_schedule["children"])
    return new_schedule


def inline(func_info, schedule):
  storage_nodes = [d for d in get_descendants(schedule) if d["type"] == STORAGE]
  all_callees = set()
  for f in func_info:
    all_callees = all_callees.union(get_callees(func_info, f))

  used_callees = [s["func"] for s in storage_nodes if s["func"] in all_callees]
  for callee in used_callees: 
    removed_func_schedule = remove_func(schedule, callee)[0]
    inlined_func_schedule = inline_func(removed_func_schedule, func_info, callee)
    yield inlined_func_schedule


def remove_inlined(schedule, inlined):
  if schedule["type"] == COMPUTE:
    if inlined in map(lambda c: c["func"], schedule["children"]):
      new_compute = copy_schedule(schedule)
      new_compute["children"] = \
          filter(lambda c: c["func"] != inlined, new_compute["children"])

      return new_compute

  else:
    new_schedule = copy_schedule(schedule)
    new_schedule["children"] = \
        map(lambda c: remove_inlined(c, inlined), new_schedule["children"])

    return new_schedule


def deinline(func_info, schedule):
  compute_nodes = [d for d in get_descendants(schedule) if d["type"] == COMPUTE]
  all_inlined = set()
  inlined_map = {}
  for node in compute_nodes:
    for inlined in node["children"]:
      all_inlined.add(inlined["func"])
      inlined_map[inlined["func"]] = inlined
        
  for inlined in all_inlined:
    dominator = schedule
    dominator_found = False
    dominator_path = []
    dominator_index = []
    while not dominator_found:
      children_with_inlined = []

      for i in range(len(dominator["children"])):
        child = dominator["children"][i]
        child_inlined = []
        for node in get_descendants(child):
          if node["type"] == COMPUTE:
            for node_inlined in node["children"]:
              child_inlined.append(node_inlined["func"])

        if any([(inlined in child_inlined) for inlined in all_inlined]):
          children_with_inlined.append((child,i))

      if len(children_with_inlined) == 1:
        common_subtree = children_with_inlined[0][0]
        common_subtree_index = children_with_inlined[0][1]

        if common_subtree["type"] != COMPUTE:
          dominator_path.append(dominator)
          dominator_index.append(common_subtree_index)
          dominator = common_subtree

        else:
          dominator_found = True

      else:
        dominator_found = True

    new_schedule = remove_inlined(dominator, inlined)

    # build new subtree for de-inlined function
    compute_inlined = copy_schedule(inlined_map[inlined])
    loop_x_inlined = loop(inlined, X_VAR, SEQUENTIAL, [compute_inlined])
    loop_y_inlined = loop(inlined, Y_VAR, SEQUENTIAL, [loop_x_inlined])
    storage_inlined = storage(inlined, [loop_y_inlined] + new_schedule["children"])

    new_schedule["children"] = [storage_inlined]

    while len(dominator_path) > 0:
      parent = copy_schedule(dominator_path.pop())
      i = dominator_index.pop()
      parent["children"][i] = new_schedule
      new_schedule = parent

    yield new_schedule


### bounds inference

def symname(func, var, n=None):
  if n is None:
    return "{}_{}".format(func, var)

  else:
    return "{}_{}_{}".format(func, var, n)

def infer_bounds(func_info, outf, schedule, width, height):
  global solver

  solver.push()

  # map from loop index variables to Z3 symbolic variables
  symvar_map = {}

  # map from loop index variable to list of possible variants
  variant_map = {}

  def expr_to_symval(caller_x, caller_y, expr):
    if expr["type"] == VAR and expr["var"] == X_VAR:
      return caller_x

    elif expr["type"] == VAR and expr["var"] == Y_VAR:
      return caller_y

    elif expr["type"] == VAR and expr["var"] in symvar_map:
      return symvar_map[expr["var"]]

    elif expr["type"] == CONST:
      return expr["val"]

    elif expr["type"] == OP:
      if expr["op"] == PLUS:
        lhs = expr_to_symval(caller_x, caller_y, expr["operands"][0])
        rhs = expr_to_symval(caller_x, caller_y, expr["operands"][1])
        return lhs + rhs

      elif expr["op"] == MINUS:
        lhs = expr_to_symval(caller_x, caller_y, expr["operands"][0])
        rhs = expr_to_symval(caller_x, caller_y, expr["operands"][1])
        return lhs - rhs

      elif expr["op"] == TIMES:
        lhs = expr_to_symval(caller_x, caller_y, expr["operands"][0])
        rhs = expr_to_symval(caller_x, caller_y, expr["operands"][1])
        return lhs * rhs

      elif expr["op"] == DIVIDE:
        lhs = expr_to_symval(caller_x, caller_y, expr["operands"][0])
        rhs = expr_to_symval(caller_x, caller_y, expr["operands"][1])
        return lhs / rhs

      else:
        raise Exception("operand " + expr["op"] + " not supported")

    else:
      raise Exception("expression type " + str(expr) + " not supported")


  for f in func_info:
    symvar_map[(f,X_VAR)] = z3.Int(symname(f,X_VAR))
    symvar_map[(f,Y_VAR)] = z3.Int(symname(f,Y_VAR))
    variant_map[(f,X_VAR)] = []
    variant_map[(f,Y_VAR)] = []

  ancestor_map = get_ancestor_map(schedule)
  visited_compute_nodes = set([(outf,X_VAR),(outf,Y_VAR)])
  visit_list = [schedule]
  while len(visit_list) > 0:
    node = visit_list.pop()

    if node["type"] in [ROOT, LOOP, STORAGE]:
      visit_list.extend(list(reversed(node["children"])))

    # only try to infer bounds for non-output functions
    elif node["type"] == COMPUTE and not node["func"] == outf:
      func = node["func"]
      visited_compute_nodes.add((func,X_VAR))
      visited_compute_nodes.add((func,Y_VAR))

      callers = get_callers(func_info, func)
      for caller in callers:
        callee_path = ancestor_map[func]
        caller_path = ancestor_map[caller]

        # find point of divergence between callee and caller path
        while (len(callee_path) > 0 and len(caller_path) > 0) \
              and callee_path[0] == caller_path[0]:
          callee_path.pop(0)
          caller_path.pop(0)

        # compute loop indices for callers by traversing path from
        # storage node to compute node; these then are multiplied together
        caller_x_list = []
        caller_y_list = []
        for node in caller_path:
          if node["type"] == LOOP and node["func"] == caller:
            if node["var"] in [X_VAR, X_INNER_VAR, X_OUTER_VAR]:
              caller_x_list.append(expr_to_symval(None, None, node["size"]))

            if node["var"] in [Y_VAR, Y_INNER_VAR, Y_OUTER_VAR]:
              caller_y_list.append(expr_to_symval(None, None, node["size"]))

        caller_x = reduce(lambda x, acc: x*acc, caller_x_list, z3.IntVal(1))
        caller_y = reduce(lambda y, acc: y*acc, caller_y_list, z3.IntVal(1))

        calls = get_calls(func_info[caller], func)
        for call in calls:
          nx = len(variant_map[(func,X_VAR)]) + 1
          ny = len(variant_map[(func,Y_VAR)]) + 1

          sym_x = z3.Int(symname(func,X_VAR,nx))
          sym_y = z3.Int(symname(func,Y_VAR,ny))

          variant_map[(func,X_VAR)].append(sym_x)
          variant_map[(func,Y_VAR)].append(sym_y)

          val_x = expr_to_symval(caller_x, caller_y, call["x"])
          val_y = expr_to_symval(caller_x, caller_y, call["y"])

          solver.add(sym_x == val_x)
          solver.add(sym_y == val_y)

  ## retrieve model to compute min and max bounds
  # f is either min or max
  def get_model_map(f, dimx, dimy):
    model_map = {}

    # compute max
    solver.push()

    # set output dimensions
    out_x = symvar_map[(outf,X_VAR)]
    out_y = symvar_map[(outf,Y_VAR)]
    solver.add(out_x == dimx)
    solver.add(out_y == dimy)

    for key in variant_map:
      # set variable to be the max of all variants
      if len(variant_map[key]) > 0:
        sym = symvar_map[key]
        variants = variant_map[key]

        for variant in variants:
          solver.add(f(sym, variant))

        eq_clause = z3.Or(*[sym == v for v in variants])
        solver.add(eq_clause)

    if solver.check() == z3.sat:
      model = solver.model()

      for key in visited_compute_nodes:
        val = model.eval(symvar_map[key])
        model_map[key] = val.as_long()

      solver.pop()

      return model_map

    else:
      raise Exception("constraints unsatisfiable!")

  max_map = get_model_map(lambda sym, variant: sym >= variant, width, height)
  min_map = get_model_map(lambda sym, variant: sym <= variant, 1, 1)

  solver.pop()

  ## compute loop sizes
  size_map = {}
  for key in visited_compute_nodes:
    val_list = [max_map[key], min_map[key]]
    size = max(val_list) - min_map[key] + 1
    size_map[key] = size

  return size_map


# annotate schedule's loop and storage nodes with sizes
def annotate_schedule_size(size_map, schedule):
  if schedule["type"] == ROOT:
    return root(map(lambda c: annotate_schedule_size(size_map, c), schedule["children"]))

  elif schedule["type"] == LOOP:
    return loop(schedule["func"], schedule["var"], schedule["loop_type"], \
              map(lambda c: annotate_schedule_size(size_map, c), schedule["children"]), \
              eval_expr(size_map, schedule["size"]))

  elif schedule["type"] == STORAGE:
    node = storage(schedule["func"], \
              map(lambda c: annotate_schedule_size(size_map, c), schedule["children"]))
    node["size"] = eval_expr(size_map, schedule["size"])
    return node

  elif schedule["type"] == COMPUTE:
    return compute(schedule["func"], map(copy_schedule, schedule["children"]))


def get_iterations(ancestry_path):
  iterations = 1
  for loop in [a for a in ancestry_path if a["type"] == LOOP]:
    if loop["type"] == SEQUENTIAL:
      iterations *= loop["size"]

  return iterations

### cost estimation



# give information about:
# - the number of arithmetic operations performed
# - the number of loads
# - the number of stores
#
# this function assumes the loops in schedule have been decorated
# with size information, computed during bounds inference
def execution_info(func_info, schedule):
  exec_info = {
    "mem": 0,
    "load": 0,
    "store": 0,
    "+": 0,
    "-": 0,
    "*": 0,
    "/": 0,
    "sin": 0,
    "cos": 0,
    "tan": 0,
    "sqrt": 0
  }

  ancestor_map = get_ancestor_map(schedule)
  visit_list = [schedule]

  while len(visit_list) > 0:
    node = visit_list.pop()

    if node["type"] in [ROOT, LOOP]:
      visit_list.extend(list(reversed(node["children"])))

    elif node["type"] == STORAGE:
      exec_info["mem"] += node["size"]

      visit_list.extend(list(reversed(node["children"])))

    elif node["type"] == COMPUTE:
      ancestry_path = ancestor_map[node["func"]]
      iterations = get_iterations(ancestry_path)
      exec_info["store"] += iterations

      inline_map = {}

      worklist = [node]
      while len(worklist) > 0:
        inline_node = worklist.pop()
        children = inline_node["children"]
        inline_map[inline_node["func"]] = [c["func"] for c in children]
        worklist.extend(children)

      def expr_execution_info(func, expr):
        if expr["type"] in [CONST, VAR]:
          pass

        elif expr["type"] == OP:
          if expr["op"] == PLUS:
            exec_info["+"] += iterations

          elif expr["op"] == MINUS:
            exec_info["-"] += iterations

          elif expr["op"] == TIMES:
            exec_info["*"] += iterations

          elif expr["op"] == DIVIDE:
            exec_info["/"] += iterations

          elif expr["op"] == SIN:
            exec_info["sin"] += iterations

          elif expr["op"] == COS:
            exec_info["cos"] += iterations

          elif expr["op"] == TAN:
            exec_info["tan"] += iterations

          elif expr["op"] == SQRT:
            exec_info["sqrt"] += iterations

          for operand in expr["operands"]:
            expr_execution_info(func, operand)

        elif expr["type"] == FUNC:
          # already saved; load from storage
          if expr["func"] not in inline_map[func]:
            exec_info["load"] += iterations
            
          # inlined
          else:
            f = expr["func"]
            fdef = func_info[f]
            expr_execution_info(f, fdef)

      expr_execution_info(node["func"], func_info[node["func"]])

  return exec_info

MEM_WEIGHT    = 0.1
LOAD_WEIGHT   = 0.5
STORE_WEIGHT  = 0.5
ARITH_WEIGHT  = 1.0
MATH_WEIGHT   = 10.0

def estimate_cost(exec_info):
  cost = 0.0
  cost += MEM_WEIGHT * float(exec_info["mem"])
  cost += LOAD_WEIGHT * float(exec_info["load"])
  cost += STORE_WEIGHT * float(exec_info["store"])

  arith_ops = exec_info["+"] + exec_info["-"] + exec_info["*"] + exec_info["/"]
  cost += ARITH_WEIGHT * float(arith_ops)

  math_ops = exec_info["sin"] + exec_info["cos"] + exec_info["tan"] + exec_info["sqrt"]
  cost += MATH_WEIGHT * float(math_ops)
  return cost


def cost_estimator(func_info):
  def wrapper(schedule):
    exec_info = execution_info(func_info, schedule)
    return estimate_cost(exec_info)

  return wrapper


def mutate(func_info, schedule):
  mutators = [deinline, hoist_storage, hoist_compute,
              split, reorder, change_loop_type, \
              lower_compute, inline]
  random.shuffle(mutators)

  for mutator in mutators:
    for mutant in mutator(func_info, schedule):
      if is_legal_schedule(func_info, mutant):
        yield mutant

# genetic algorithm search
NUM_GENERATIONS = 10
POPULATION_SIZE = 300
SELECTION_NUM   = 300

def search_schedule(func_info, outf, width, height, debug=False):
  estimator = cost_estimator(func_info)

  default = default_schedule(func_info, outf)
  size_map = infer_bounds(func_info, outf, default, width, height)
  annot_default = annotate_schedule_size(size_map, default)

  population = [(default,annot_default)]

  gen = 1
  while gen < NUM_GENERATIONS:
    if debug:
      print "generation", str(gen), "population", str(len(population))
      print "best schedule, cost", round(estimator(population[0][1]), 2)
      print_schedule(population[0][1])

    # "roulette" selection
    pop_inv_cost = [(s,1.0/estimator(a)) for (s,a) in population]
    total = sum(map(lambda (s,c): c, pop_inv_cost))

    selected_list = [s for (s,a) in population]
    # selected_list = []
    # for i in range(SELECTION_NUM):
    #   n = total * random.random()
    #   p = 0.0

    #   for s,c in ((s,c) for (s,c) in pop_inv_cost if s not in selected_list):
    #     p += c
    #     if p >= n:
    #       selected_list.append(s)
    #       total -= c
    #       break

    # mutation
    for selected in selected_list:
      for mutant in mutate(func_info, selected):
        size_map = infer_bounds(func_info, outf, mutant, width, height)
        annot_mutant = annotate_schedule_size(size_map, mutant)
        population.append((mutant, annot_mutant))

    # only keep the fittest
    population.sort(key=(lambda (s,a): a), \
        cmp=lambda s1, s2: int(estimator(s1) - estimator(s2)))
    population = population[:POPULATION_SIZE]
    gen += 1

  return population[0][1]


DEPTH       = 10
BEAM_WIDTH  = 300
def beam_search_schedule(func_info, outf, width, height, debug=False, \
                          depth=DEPTH, beam_width=BEAM_WIDTH):

  estimator = cost_estimator(func_info)

  default = default_schedule(func_info, outf)
  size_map = infer_bounds(func_info, outf, default, width, height)
  annot_default = annotate_schedule_size(size_map, default)

  population = [(default,annot_default)]
  best = population[0]

  gen = 1
  while gen < depth and len(population) > 0:
    if debug:
      print "generation", str(gen), "population", str(len(population))
      print "best schedule, cost", round(estimator(best[1]), 2)
      print_schedule(best[1])

    next_gen = []
    for selected in (s for (s,a) in population):
      for mutant in mutate(func_info, selected):
        size_map = infer_bounds(func_info, outf, mutant, width, height)
        annot_mutant = annotate_schedule_size(size_map, mutant)
        next_gen.append((mutant, annot_mutant))

    # only keep the fittest
    next_gen.sort(key=(lambda (s,a): a), \
        cmp=lambda s1, s2: int(estimator(s1) - estimator(s2)))
    population = next_gen[:beam_width]

    if estimator(best[1]) > estimator(population[0][1]):
      best = population[0]

    gen += 1

  return best[1]

### convert schedule tree into halide code

def convert_to_halide(func_info, out_f, schedule, width, height):
  instructions = []

  # instructions variables and function defs
  vars_str = ",".join([X_VAR, X_OUTER_VAR, X_INNER_VAR, Y_VAR, Y_OUTER_VAR, Y_INNER_VAR])
  instructions.append("Var {};".format(vars_str))

  funcs_str = ",".join(["{}(\"{}\")".format(f, f) for f in func_info])
  instructions.append("Func {};".format(funcs_str))

  instructions.append("")
  for f, fdef in func_info.items():
    fdef_str = print_expr(fdef)
    instructions.append("{}({},{}) = {};".format(f, X_VAR, Y_VAR, fdef_str))


  # scheduling instructions
  ancestor_map = get_ancestor_map(schedule)
  for f, ancestors in ancestor_map.items():
    instructions.append("")
    f_loops = [a for a in ancestors if a["type"] == LOOP and a["func"] == f]
    f_loop_vars = [f_loop["var"] for f_loop in f_loops]
    is_x_split = X_INNER_VAR in f_loop_vars
    is_y_split = Y_INNER_VAR in f_loop_vars

    if is_x_split:
      x_split_factor = f_loops[f_loop_vars.index(X_INNER_VAR)]["size"]
      x_split_instr = \
          "{}.split({},{},{},{});".format(f, X_VAR, X_OUTER_VAR, X_INNER_VAR, x_split_factor)
      instructions.append(x_split_instr)

    if is_y_split:
      y_split_factor = f_loops[f_loop_vars.index(Y_INNER_VAR)]["size"]
      y_split_instr = \
          "{}.split({},{},{},{});".format(f, Y_VAR, Y_OUTER_VAR, Y_INNER_VAR, y_split_factor)
      instructions.append(y_split_instr)

    # set loop order
    reorder_instr = "{}.reorder({});".format(f, ",".join(reversed(f_loop_vars)))
    instructions.append(reorder_instr)

    # set loop types
    f_loops_nonseq = [f_loop for f_loop in f_loops if f_loop["loop_type"] != SEQUENTIAL]
    for f_loop in f_loops_nonseq:
      if f_loop["loop_type"] == VECTORIZED:
        vectorize_instr = "{}.vectorize({},{});".format(f, f_loop["var"], f_loop["size"])
        instructions.append(vectorize_instr)

    # set call order (storage and compute locations)
    if f != out_f:
      rev_ancestors = list(reversed(ancestors))

      # the closest loop for a different function is the place where we compute
      found_store_loc = False
      found_compute_loc = False
      storage_ind = -1
      for i in range(len(rev_ancestors)):
        a = rev_ancestors[i]
        if not found_compute_loc and a["type"] == LOOP and a["func"] != f:
          compute_instr ="{}.compute_at({},{});".format(f, a["func"], a["var"])
          instructions.append(compute_instr)
          found_compute_loc = True

        if not found_store_loc and storage_ind >= 0 \
            and a["type"] == LOOP and a["func"] != f:
          store_instr = "{}.store_at({},{});".format(f, a["func"], a["var"])
          instructions.append(store_instr)
          found_store_loc = True

        if a["type"] == STORAGE and a["func"] == f:
          storage_ind = i

      if not found_compute_loc:
        instructions.append("{}.compute_root();".format(f))

      if not found_store_loc:
        instructions.append("{}.store_root();".format(f))

  realize_instr = "{}.realize({},{});".format(f, width, height)
  instructions.append(realize_instr)
  return instructions

### example

# func_info = {
#   "f": plus(func("g", plus(x(), const(1)), y()), func("g", x(), y())),
#   "g": sqrt(times(x(), y()))
# }
# 
# s1 = default_schedule(func_info, "f")
# size_map1 = infer_bounds(func_info, "f", s1, 512, 512)
# s1a = annotate_schedule_size(size_map1, s1)
# 
# s2 = list(deinline(func_info, s1))[0]
# 
# s3 = list(hoist_storage(func_info, s2))[0]
# 
# s4 = list(hoist_compute(func_info, s3))[0]
# size_map4 = infer_bounds(func_info, "f", s4, 512, 512)
# s4a = annotate_schedule_size(size_map4, s4)


