# Idris Satyr

Bindings for SAT and SMT solvers as an Idris2 library.

This project is in early stages, and much of it is likely to change.

# Sources

Satyr use the [SMT-LIB](https://smtlib.cs.uiowa.edu) standard.  This
standard specifies a common format for defining theories and logics
that common SMT solvers adhere to, and a scripting language for
interacting with these solvers. It also defines basic shared theories
that these solvers will implement.

To ease maintenance, Satyr uses the SMT-LIB format to generate Idris2
definitions out of the SMT-LIB common interface. While Satyr ships
with these generated definitions, it is possible to re-generate them
and pin them to a specific version of the SMT-LIB standard by cloning
the SMT-LIB submodule, located under `suppoer/smtlib/gitlab-submodule`.

## Working with the SMT-LIB submodules

You can read more about git submodules in the
[manual](https://git-scm.com/book/en/v2/Git-Tools-Submodules). A short
cheatsheet:

### To initialise the submodules

* The easiest way to do so is to clone the Satyr repository together
  with its submodules, for example:

  ```bash
  ~/dev$ git clone git@github.com:ohad/idris-satyr.git --recurse-submodules
  ```

* If you already cloned the repo but want to get the same effect, use,
  for example:

  ``` bash
  ~/dev/idris-satyr$ git submodule update --init --recursive
  ```
