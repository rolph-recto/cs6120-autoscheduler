#!/usr/bin/env python

import itertools
import z3

### utils

def flatten(lst):
  return [item for elem in lst for item in elem]


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
    "size": const(0),
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
    print "storage", schedule["func"]
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
    return loop(schedule["func"], schedule["var"], schedule["loop_type"], \
              map(copy_schedule, schedule["children"]), \
              copy_expr(schedule["size"]))

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
  funcs = []
  node_list = [func_info[func]]

  while len(node_list) > 0:
    node = node_list.pop()

    if node["type"] == FUNC:
      funcs.append(node["func"])

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
          print "vectorizing loop that is not innermost"
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
          print "function not a storage ancestor"
          return False

        # illegal: storage must be an ancestor of called functions
        if f not in inlined_funcs and f not in storage_ancestors:
          print "called function not a storage ancestor"
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
        if schedule["size"] % split_factor == 0:
          inner_loop = loop(schedule["func"], split_vars[1], \
              schedule["loop_type"], schedule["children"], const(split_factor))
          outer_loop = loop(schedule["func"], split_vars[0], \
              schedule["loop_type"], [inner_loop], divide(schedule["size"], split_factor))

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

    loop_types = [SEQUENTIAL, PARALLEL, VECTORIZED]
    for new_loop_type in filter(lambda x: x != schedule["loop_type"], loop_types):
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


def symname(func, var, n=None):
  if n is None:
    return "{}_{}".format(func, var)

  else:
    return "{}_{}_{}".format(func, var, n)

### bounds inference
def infer_bounds(func_info, schedule, outf, width, height):
  solver = z3.Solver()

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
        raise ("operand " + expr["op"] + " not supported")

    else:
      raise ("expression type " + str(expr) + " not supported")


  for f in func_info:
    symvar_map[(f,X_VAR)] = z3.Int(symname(f,X_VAR))
    symvar_map[(f,Y_VAR)] = z3.Int(symname(f,Y_VAR))
    variant_map[(f,X_VAR)] = []
    variant_map[(f,Y_VAR)] = []

  ancestors = [] 
  visit_list = [schedule]
  while len(visit_list) > 0:
    node = visit_list.pop()

    if node["type"] == SENTRY:
      ancestors.pop()

    elif node["type"] == ROOT:
      visit_list.append(sentry())
      visit_list.extend(list(reversed(node["children"])))
      ancestors.append(node)

    elif node["type"] == LOOP:
      # create symbolic values 

      visit_list.append(sentry())
      visit_list.extend(list(reversed(node["children"])))
      ancestors.append(node)

    elif node["type"] == STORAGE:
      visit_list.append(sentry())
      visit_list.extend(list(reversed(node["children"])))
      ancestors.append(node)

    # only try to infer bounds for non-output functions
    elif node["type"] == COMPUTE and not node["func"] == outf:
      func = node["func"]
      storage_path = list(ancestors)
      while not (storage_path[0]["type"] == STORAGE and storage_path[0]["func"] == func):
        storage_path.pop(0)

      callers = get_callers(func_info, func)
      for caller in callers:
        # compute loop indices for callers by traversing path from
        # storage node to compute node; these then are multiplied together
        caller_x_list = []
        caller_y_list = []
        for node in storage_path:
          if node["type"] == LOOP and node["func"] == caller:
            if node["var"] in [X_VAR, X_INNER_VAR, X_OUTER_VAR]:
              caller_x_list.append(expr_to_symval(None, None, node["size"]))

            if node["var"] in [Y_VAR, Y_INNER_VAR, Y_OUTER_VAR]:
              caller_y_list.append(expr_to_symval(None, None, node["size"]))

        caller_x = reduce(lambda x, acc: x*acc, caller_x_list, 1)
        caller_y = reduce(lambda y, acc: y*acc, caller_y_list, 1)

        
        map(lambda p: print_schedule(p), storage_path)
        print caller, caller_x, caller_y

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

  # check if satisfiable and retrieve model
  for key in variant_map:
    # set variable to be the max of all variants
    if len(variant_map[key]) > 0:
      sym = symvar_map[key]
      variants = variant_map[key]

      for variant in variants:
        solver.add(sym >= variant)

      # eq_clause = reduce(lambda v, acc: z3.Or(acc, sym == v), variants)
      # solver.add(eq_clause)

  # set output dimensions
  out_x = symvar_map[(outf,X_VAR)]
  out_y = symvar_map[(outf,Y_VAR)]
  solver.add(out_x == width)
  solver.add(out_y == height)

  if solver.check() == z3.sat:
    model = solver.model()

    for key in symvar_map:
      val = model.eval(symvar_map[key])
      print "model: ", key, " = ", val

  else:
    print "constraints unsatisfiable!"

# give information about:
# - the number of arithmetic operations performed
# - the number of loads
# - the number of stores
#
# this function assumes the loops in schedule have been decorated
# with size information, computed during bounds inference
def execution_info(func_info, schedule):
  loads = 0
  stores = 0
  operations = 0
  ancestors  = []
  visit_list = [schedule]

  while len(visit_list) > 0:
    node = visit_list.pop()
    upstream_loops = [a for a in ancestors if a["type"] == LOOP]
    iterations = reduce(lambda x,y: x*y, [loop["size"] for loop in upstream_loops], 1)

    if node["type"] == SENTRY:
      ancestors.pop()

    elif node["type"] == ROOT:
      visit_list.append(sentry())
      visit_list.extend(list(reversed(node["children"])))
      ancestors.append(node)

    elif node["type"] == LOOP:
      visit_list.append(sentry())
      visit_list.extend(list(reversed(node["children"])))
      ancestors.append(node)

    elif node["type"] == STORAGE:
      stores += (iterations * node["size"])

      visit_list.append(sentry())
      visit_list.extend(list(reversed(node["children"])))
      ancestors.append(node)

    elif node["type"] == COMPUTE:
      cur_node = node
      expr_list = [func_info[node["func"]]]
      inlined_funcs = [c["func"] for c in cur_node["children"]]

      while len(expr_list) > 0:
        expr = expr_list.pop()
        if expr["type"] == CONST:
          pass

        elif expr["type"] == VAR:
          pass

        elif expr["type"] == OP:
          operations += iterations
          expr_list.extend(expr["operands"])

        elif expr["type"] == FUNC:
          # already saved; load from storage
          if expr["func"] not in inlined_funcs:
            loads += iterations

          # inlined, so we need to compute
          else:
            f = func_info[expr["func"]]
            expr_list.append(f)

            for c in cur_node["children"]:
              if c["func"] == expr["func"]:
                cur_node = c
                break

            inlined_funcs = [c["func"] for c in cur_node["children"]]

  return {
    "loads": loads,
    "stores": stores,
    "operations": operations
  }


func_info = {
  "f": plus(func("g", x(), y()), const(1)),
  "g": const(2)
}

s1 = default_schedule(func_info, "f")
s2 = list(deinline(func_info, s1))[0]
s3 = list(hoist_storage(func_info, s2))[0]

# use Z3 for bounds inference
# q(x, y) = x * y
# p(x, y) = q(x,y) - q(x+1, y+1)
# c(x,y)  = p(x,y) + p(x+1, y+1)
#
# (declare-const cx Int)
# (declare-const cy Int)
# 
# (declare-const px1 Int)
# (declare-const py1 Int)
# (declare-const px2 Int)
# (declare-const py2 Int)
# (declare-const px Int)
# (declare-const py Int)
# 
# (declare-const qx1 Int)
# (declare-const qy1 Int)
# (declare-const qx2 Int)
# (declare-const qy2 Int)
# (declare-const qx Int)
# (declare-const qy Int)
# 
# (assert (= px1 (+ cx 1)))
# (assert (= py1 (+ cy 1)))
# (assert (= px2 cx))
# (assert (= py2 cy))
# (assert (and (<= px px1) (<= px px2) (or (= px px1) (= px px2))))
# (assert (and (<= py py1) (<= px py2) (or (= py py1) (= py py2))))
# 
# (assert (= qx1 (+ px 1)))
# (assert (= qy1 (+ py 1)))
# (assert (= qx2 px))
# (assert (= qy2 py))
# (assert (and (<= qx qx1) (<= qx qx2) (or (= qx qx1) (= qx qx2))))
# (assert (and (<= qy qy1) (<= qx qy2) (or (= qy qy1) (= qy qy2))))
# 
# (assert (= cx 1))
# (assert (= cy 1))
# (check-sat)
# (get-model)


