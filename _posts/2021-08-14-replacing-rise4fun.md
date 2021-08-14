---
author: Philip Zucker
date: 2021-08-14
layout: post
title: "Replicating Rise4Fun Z3 with z3-wasm"
tags:
  - z3
  - smt
  - wasm
---

Rise4Fun was a very cool demo page for projects at Microsoft Research. I think it was fantastic. But it may have finally [died](https://github.com/Z3Prover/z3/discussions/5473)

First off, just check this out <https://www.philipzucker.com/z3-rise4fun/> (not on mobile). A Z3 right in your browser! Neat right?


### Compiling to the Web
I'm a big proponent of compiling to the web. Ultimately, nearly no one cares about you or what you do. Think about how many people who's work you care about. I see quite a number of very cool and impressive projects every day. The number I spend the time to download and install is very few. I cannot expect others to be more proactive about seeking out my work than I am of theirs.

So it behooves you if you care about having your work seen to make the barrier as low as possible. The lowest barrier way of doing this that I know of is compiling to the web.

Another great thing about compiling to the web is you can use static hosting. It is tempting and simple sounding to just make a server that runs ruquests for your project on the backend. I don't do it, perhaps because I'm stuck on github.io hosting. Github.io hosting is so useful and easy though. I love it. In addition your server will probably be a little wonky, definitely a little complicated, probably insecure, especially if you're evaluating semi-arbitrary queries in some kind of programming language.

I've explored:

- Egglog <https://www.philipzucker.com/egglog2-monic/>
- An egg based prover <https://www.philipzucker.com/rust-category/>
- Minikanren and scheme <https://www.philipzucker.com/aop-minikanren/>
- Tau Prolog theorem prover <https://www.philipzucker.com/javascript-automated-proving/>

And all of them are basically the same thing. I have an input textarea, run button, and a results div.

```html
<script>
 function run(){
     var query = document.getElementById("query").value;
     result = do_my_cool_stuff(query);
     document.getElementById("result").value = result;

 }
</script>
<textarea id="query" rows="20" style="width:100%">
</textarea>
<button onclick="run()">Run</button>
<code id="result" style="white-space:pre-wrap"> </code>
```

If you want to compile to the web you need to use a little javascript as glue. You can do the whole thing in javascript if you like. It's actually kind of a nice language in many ways. But I'm into stupid weirdo languages, so I've had fun with

- ocaml js_of_ocaml
- rust wasm
- emscripten - C/C++

There are also some languages where the full runtime is just a javascript script

- Tau Prolog <http://tau-prolog.org/>
- BiwaScheme <https://www.biwascheme.org/>
- Minikanren on biwascheme <https://www.philipzucker.com/aop-minikanren/>

### Notes on getting Z3-wasm to work

I made some edits to the build script from here <https://github.com/bramvdbogaerde/z3-wasm> in particular to include pthreads to make z3 work.

```bash
#!/usr/bin/env bash

if [ -z $Z3_BASE_DIR ]; then
   export Z3_BASE_DIR="$PWD/z3"
fi

if [ -z $Z3_VERSION ]; then
   export Z3_VERSION="z3-4.8.10"
fi

export ROOT=$PWD

function available() {
   echo "Checking if $1 is available"
   if ! [ -x $(command -v $1) ]; then
      echo "Error $1 is not installed" >&2
      exit 1
   fi
}


available emcc
available emconfigure

mkdir -p out
mkdir -p $Z3_BASE_DIR

cd $Z3_BASE_DIR
git clone https://github.com/Z3Prover/z3 .
git fetch --all --tags
git checkout $Z3_VERSION 

CXXFLAGS="-pthread -s DISABLE_EXCEPTION_CATCHING=0 -s USE_PTHREADS=1" emconfigure python scripts/mk_make.py --staticlib
cd build
emmake make -j$(nproc)

cd $ROOT

export EM_CACHE=$HOME/.emscripten/
emcc api/api.c $Z3_BASE_DIR/build/libz3.a -fexceptions -pthread -s EXPORTED_FUNCTIONS='["_init_context", "_destroy_context", "_eval_smt2"]' -s DISABLE_EXCEPTION_CATCHING=0 -s EXCEPTION_DEBUG=1 -s USE_PTHREADS=1 -s PTHREAD_POOL_SIZE=4 -s TOTAL_MEMORY=1GB -I $Z3_BASE_DIR/src/api/ --post-js api/api.js -o out/z3.js

```

Turn on https for github.io or it won't work!

After building, inclusion of Z3 is very simple. 

```html
<script src="out/z3.js"> </script>

```
And to make a z3 query in smtlib format it is as easy as 
```javascript
console.log(Z3.solve("(echo \"Hello world\")"));
```

You can find the already compiled version of 4.8.10 in this folder. <https://github.com/philzook58/z3-rise4fun/tree/master/out> You may need to host it yourself, because there are funny permission issues going on.

I went to an archive.org <https://web.archive.org/web/20210119175613/https://rise4fun.com/Z3/tutorial/guide> to get the frame source of the old rise4fun z3 demo and literally copied it. I started hand converting the old style of code examples to my above textarea form, but I eventually realized it would be easier to do this programmatically.

```javascript
var z3_loaded = false;
window.onload = function () {
    // If the user tried to run z3 before it was loaded, it destroyed the webpage. I gated this by added 
    Z3["onInitialized"] = () => { console.log("z3 loaded"); z3_loaded = true; }

    // Grab all pre elements and replace them with textarea button results combo
    var examples = document.getElementsByTagName("pre");
    console.log(examples)
    examples = Array.from(examples)
    for (let code of examples) {
        if (code.className == "listing") {
            let div = document.createElement("div");

            let ta = document.createElement("textarea");
            let result = document.createElement("code");
            result.style.whiteSpace = "pre-wrap";

            let button = document.createElement("button");
            let br = document.createElement("br");

            ta.style.width = "100%";
            ta.innerHTML = code.textContent.replace(/\r?\n/g, '\r\n');
            //code.parentNode.replaceChild(ta, code);
            button.innerText = "Run"
            button.onclick = () => {
                if (z3_loaded) {
                    try {
                        let res = Z3.solve(ta.value);
                        console.log(res)
                        result.innerText = res;
                    } catch (error) {
                        console.error(error);
                        result.innerText = "Error. See Javascript console for more detail";
                    }
                } else {
                    result.innerText = "Wait for Z3 to load and try again."
                }
            }
            div.appendChild(ta);
            div.appendChild(button);
            div.appendChild(br);
            div.appendChild(result);
            code.parentNode.replaceChild(div, code);
        }
    }

    // destroy aref that do nothing now
    var badlinks = document.getElementsByTagName('a');
    for (var i = 0; i < badlinks.length; i++) {
        link = badlinks[i]
        if (link.innerHTML == "load in editor") {
            link.innerHTML = ""
            //link.remove()

        }
    }

    // resize rows of all textarea to fits code 
    var inputs = document.getElementsByTagName('textarea');
    for (var i = 0; i < inputs.length; i++) {
        inputs[i].rows = Math.min(20, inputs[i].value.split(/\r\n|\r|\n/).length - 1);
    }

}
```


I had some problems with modern browsers disallowing SharedBufferArray access without some curious http headers set. I was pointed to this project <https://github.com/gzuidhof/coi-serviceworker> which has a script which seems to have fixed the problem.

### Known problems
- Non smtlib commands don't work such as optimization or fixedpoint commands. Probably because of the function we're using to call z3 being a stock smtlib function.
- On main thread, so a tough Z3 query can make the tab unusable. I think there is a emscripten flag for this PROXY_TO_PTHREAD <https://emscripten.org/docs/porting/pthreads.html> 
- I can't find copies of some of the smtlib commands that do not appear to be on the archive.org site.
- Doesn't seem to load on my iPhone. Why?

### other Z3 Javascript Projects
There are many Z3 in browser projects. I think pit-claudel's is the OG?

- <https://github.com/cpitclaudel/z3.wasm>
- <https://github.com/Z3Prover/z3/issues/1298>
- <https://github.com/babelsberg/z3.js>
- <https://github.com/sim642/z3em>
- <https://github.com/mjyc/z3js>
- <https://github.com/stahlbauer/z3.ts>










