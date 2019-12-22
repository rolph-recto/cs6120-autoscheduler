#!/usr/bin/env python

import os
from autoscheduler import *

TESTS_DIR = "tests"

tests = {
  "test1": {
    "out": "f",
    "width": 2048,
    "height": 2048,
    "func_info": {
      "f": plus( \
          plus(func("g", plus(x(), const(1)), y()), func("g", x(), y())), \
          plus(func("g", plus(x(), const(1)), plus(y(), const(1))), \
               func("g", x(), plus(y(), const(1))))),
      "g": sqrt(plus(cos(x()), sin(y())))
    }
  },
  "test2": {
    "out": "blur_y",
    "width": 2048,
    "height": 2048,
    "func_info": {
      "input": const(0),
      "blur_x": divide(plus( \
                  plus(func("input", minus(x(), const(1)), y()), func("input", x(), y())), \
                  func("input",plus(x(),const(1)),y())), const(3)),
      "blur_y": divide(plus( \
                  plus(func("blur_x", minus(x(), const(1)), y()), func("blur_x", x(), y())), \
                  func("blur_x",plus(x(),const(1)),y())), const(3))
    }
  },
  "test3": {
    "out": "f",
    "width": 2048,
    "height": 2048,
    "func_info": {
      "f": plus(x(), y())
    }
  }
}

for test, info in tests.items():
  print "searching schedule for", test

  func_info = info["func_info"]
  outf = info["out"]
  width = info["width"]
  height = info["height"]

  schedule = beam_search_schedule(func_info, outf, width, height, debug=True)
  instrs = convert_to_halide(func_info, outf, schedule, width, height)

  testfile = "{}.cpp".format(test)
  with open(os.path.join(TESTS_DIR,testfile), "w") as f:
    for instr in instrs:
      f.write(instr + "\n")


