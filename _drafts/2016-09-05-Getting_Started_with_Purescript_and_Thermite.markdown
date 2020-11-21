---
author: philzook58
comments: true
date: 2016-09-05 20:00:36+00:00
layout: post
link: https://www.philipzucker.com/?p=501
published: false
slug: Getting Started with Purescript and Thermite
title: Getting Started with Purescript and Thermite
wordpress_id: 501
---

I'm intrigued by purescript. Haskell on the web. Sounds good? Despite what people say, I still believe the nature of Haskell's construction make IO pretty painful, monad or no. I like a lot of other bits, but having to go into kind of a confusing mind space to do stuff that is usually easy sucks.

The web is heavy in the IO. In that sense purescript sounds bad. But, maybe other benefits outweigh this.



[http://www.purescript.org/learn/getting-started/](http://www.purescript.org/learn/getting-started/)

Install purescript with npm

    
    npm install -g purescript
    npm install -g pulp bower


Make a new folder and pulp init in it.

So it's a good idea to check out the pulp github to see some of what it can do

[https://github.com/bodil/pulp](https://github.com/bodil/pulp)

pulp build: compiles

pulp run: runs the program

pulp psci: brings up the REPL, which can be invaluable for answering syntax or what will this do questions.

    
    pulp browserify --to bundle.js


This is going to be a useful one. The main purescript documentation seems to refer to running in a node.js context rather than in the browser. Browserifying builds a bundle.js that you can import in the browser.

    
    <!DOCTYPE html>
    <html>
    <head>
    	<title>Thermite test</title>
    	<script src="./bundle.js"> </script>
    </head>
    <body>
    YOYO
    </body>
    </html>


Open up this webpage and the console will print out whatever your main purescript guy is doing.

Now, I think we're going to want webpack running. My understanding is webpack is sort of beating out browserify and other guys and the pulp github mentions you might want to do this.

https://www.youtube.com/watch?v=9kJVYpOqcVU

This seems like a good intro video.

[https://webpack.github.io/docs/tutorials/getting-started/](https://webpack.github.io/docs/tutorials/getting-started/)

[https://github.com/ethul/purs-loader](https://github.com/ethul/purs-loader) Going to need this plugin for webpack to compile .purs files



    
    npm init
    npm install webpack-dev-server



    
    <code>npm install purs-loader --save-dev</code>


Put something like this in  a file webpack.config.js

    
    module.exports = {
        entry: "./entry.js",
        output: {
            path: __dirname,
            filename: "bundle.js"
        },
        module: {
            loaders: [
                {
                  test: /\.purs$/,
                  loader: 'purs-loader',
                  exclude: /node_modules/,
                  query: {
                    psc: 'psa',
                    src: ['bower_components/purescript-*/src/**/*.purs', 'src/**/*.purs']
                  }
                }
            ]
        }
    };


entry.js just has a require statement that imports and runs main for the moment

    
    require('./src/Main.purs').main();




    
    <code>npm install -g purescript-psa</code>


I was getting a funny error until I did this.

Got another funny error about --ffi option

    
      var args = dargs(Object.assign({
        _: options.src,
       // ffi: options.ffi,
        output: options.output
      }, options.pscArgs));


I went into the purs-loader directory and index.js and commented out the ffi option line 170. Seems to compile now.

if you npm install webpack-dev-server you can run it with

    
    ./node_modules/.bin/webpack-dev-server




    
     bower install --save purescript-thermite


There are couple of interesting options for how to deal with the DOM. Pux, Halogen, and Thermite. I'm gonna try Thermite first. It's React based


