---
author: philzook58
comments: true
date: 2016-04-29 14:00:28+00:00
layout: post
link: https://www.philipzucker.com/monads-are-still-fed-up-but-good/
slug: monads-are-still-fed-up-but-good
title: Monads are still f'ed up, but good?
wordpress_id: 406
---

[Previous Look at Monads](http://philzucker.nfshost.com/wordpress/?p=77)

I will help no one. See

[https://byorgey.wordpress.com/2009/01/12/abstraction-intuition-and-the-monad-tutorial-fallacy/](https://byorgey.wordpress.com/2009/01/12/abstraction-intuition-and-the-monad-tutorial-fallacy/)

Coming back in I think monads make more sense? The pattern is for taking out boiler plate pass along data into a single location. For instance the Maybe monad takes the constant checking for if variables exist out into a single function instead of checking every single time you're passing something that may throw an error.

For example (btw I can't really confirm this is actually a monad since I'm groping in the dark here) a common pattern in javascript is to pass in two arguments to a callback function, the error and the actual data. And then every time you make a callback function you need to check if there is an error and if the data is non null before you do your real work. I've had a ton of server crashing from this because the database may not toss a null or error for a long time and I don't notice I forgot. One could easily convert a callback function that doesn't check for errors into one by passing it into and errorize function.




    
    function errorize(cb){
    return function(err,x){
     
    if x != null && err == null
     
    cb(x)
     
    }
     
    }


Now, this doesn't really quite fit the monad paradigm, since cb should somehow return the combo (err, result) allowing for chaining, which we could do with an object for example, but that isn't how the err is traditionally wired.

Some more interesting stuff. Haskell is confusing (Maybe intrinsically but mostly because of unfamiliarity) but check out these. Comforting familiar python, like mother's bosom.

[http://www.dustingetz.com/2012/04/07/dustins-awesome-monad-tutorial-for-humans-in-python.html](http://www.dustingetz.com/2012/04/07/dustins-awesome-monad-tutorial-for-humans-in-python.html)

[http://www.valuedlessons.com/2008/01/monads-in-python-with-nice-syntax.html](http://www.valuedlessons.com/2008/01/monads-in-python-with-nice-syntax.html)

[https://github.com/dbrattli/OSlash/wiki/Functors,-Applicatives,-And-Monads-In-Pictures](https://github.com/dbrattli/OSlash/wiki/Functors,-Applicatives,-And-Monads-In-Pictures)




[https://pypi.python.org/pypi/PyMonad/](https://pypi.python.org/pypi/PyMonad/)
