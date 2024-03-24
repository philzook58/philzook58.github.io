
Packaging binaries for pip installation

I have been enjoying pyproject.toml.

A low brow way of packaging up a binary for usage and installation by pypi is to just put the binary in the folder and setup your pyproject to include it.

I'm figuring it out here <https://github.com/philzook58/pyvampire/blob/main/pyproject.toml>

static builds are preferable

I got the good idea of wrapping stuff here
<https://simonwillison.net/2022/May/23/bundling-binary-tools-in-python-wheels/>

cibuildwheel is what Ian suggested. This does look pretty good.

One way is to use setuptools to run a build. `build_ext` See pypcode

`python3 -m build` will make a wheel

# Cosmo

Cosmopolitan is a tempting thing that might get you OS interoperability

notes. Editted std/unistd to just unistd in picosat. Also in picosat remove CC setting line. I also need to make `export AR="cosmo-ar "
removed CC setting line in eprover makefile. Actually maybe`make CC=../cosmoyada` would've worked.

```
make CC=$(pwd)/../bin/unknown-unknown-cosmo-cc AR="$(pwd)/../bin/unknown-unknown-cosmo-ar rcs" RANLIB=$(pwd)/../bin/unknown-unknown-cosmo-ranlib 
```

picosat is annoying in CONTRIB. Need to abstract out ar, ranlib
   $(LN) ../$$subdir/.aarch64/$$subdir.a ./.aarch64;\ at line 146 of the Makefile.
There is a copy step into lib which needs to also copy the aarch64 verison.

distutils

I wish I hadn't done poetry in snakelog

Something I've been a bit of a tear on is wrapping external python projects that are not set up as packages into packages.

Three projects which I think are phenomenal but not set up as packages are:

- PyRes <https://github.com/eprover/PyRes> . This contains a TPTP parser and printer, and full resolution provers by one of the masters of the field.
- holpy <https://github.com/bzhan/holpy> <https://arxiv.org/abs/1905.05970> There is a preposterous amount of functionality here.
- metamath <https://github.com/david-a-wheeler/mmverify.py> A very simple module

The basic layout of a python package is to have folder with the name of the package which has a `__init__.py` file in it. You can make a package with a `pyproject.toml` these days. You don't even have to upload to the PyPI repository, and you can still install via pi by giving it the url of the repo.

- git submodule. This is nice because it is totally
- branch

A problem is the way these project may reference their other files.
