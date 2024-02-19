
Something I've been a bit of a tear on is wrapping external python projects that are not set up as packages into packages.

Three projects which I think are phenomenal but not set up as packages are:

- PyRes <https://github.com/eprover/PyRes> . This contains a TPTP parser and printer, and full resolution provers by one of the masters of the field.
- holpy <https://github.com/bzhan/holpy> <https://arxiv.org/abs/1905.05970> There is a preposterous amount of functionality here.
- metamath <https://github.com/david-a-wheeler/mmverify.py> A very simple module

The basic layout of a python pakcage is to have folder with the name of the package which has a `__init__.py` file in it. You can make a package with a `pyproject.toml` these days. You don't even have to upload to the PyPI repository, and you can still install via pi by giving it the url of the repo.

- git submodule. This is nice because it is totally
- branch

A problem is the way these project may reference their other files.
