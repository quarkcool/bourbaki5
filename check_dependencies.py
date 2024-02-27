# -*- coding: UTF-8 -*-

"""
Simple script to check that we have no redundant dependency.
"""

import sys

error = False

def check_dependencies(initial_file, dep, dependencies, known_deps=[]):
  global error

  if dependencies.has_key(dep):
    deps = dependencies[dep]

    for dep in deps:
      if dep in known_deps:
        print("Duplicate dependency for " + initial_file + "; dup: " + dep)
        error = True
      else:
        check_dependencies(initial_file, dep, dependencies, known_deps + deps)

def check_extension(name):
  return name[-3:] == ".vo"

def main():
  try:
    f = open(".CoqMakefile.d", "r")
  except:
    sys.exit(0)

  lines = f.readlines()

  dependencies = {}

  for line in lines:
    files, deps = line.split(":")

    files = filter(check_extension, files.strip().split())
    deps = filter(check_extension, deps.strip().split())

    for file in files:
      dependencies[file] = deps

  for file in dependencies.keys():
    check_dependencies(file, file, dependencies)

if __name__ == "__main__":
  main()

  if error:
    sys.exit(1)