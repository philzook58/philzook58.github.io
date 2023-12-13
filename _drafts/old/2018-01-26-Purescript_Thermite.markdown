---
author: philzook58
comments: true
date: 2018-01-26 12:59:42+00:00
layout: post
link: https://www.philipzucker.com/?p=937
published: false
slug: Purescript Thermite
title: Purescript Thermite
wordpress_id: 937
---

How does Thermite work?

Thermite is a purescript layer over organizing

http://blog.functorial.com/posts/2015-11-20-Thermite.html

Now it is a great feature of functional programming that programs end up being short. The entirety of Thermite is under 500 lines (With quite a bit of commenting).



There is a paradigm you can see in a couple different places of how to organize a web app.

Events get fired. Events can be clicks or receiving back web data or what have you. In this case the events are called Actions. Same diff I guess.

You also have State. State is whatever data you need to render the entire page. In principle, I suppose that the entire html could be the state. but the intent is to keep the state pretty small, like data entires in a list or a counter value. In MVC talk, this is the Model

Then you have a method that transforms and old state into a new state given an action. This is roughly the C

And you have a render function that given a state builds the html basically. This is the V.

The render and performAction functions are held in the Spec type

    
    newtype Spec eff state props action = Spec
      { performAction      :: PerformAction eff state props action
      , render             :: Render state props action
    }



    
    <span class="pl-en">spec</span> <span class="pl-k">::</span> <span class="pl-en">T.Spec</span> <span class="pl-smi">_</span> <span class="pl-en">State</span> <span class="pl-smi">_</span> <span class="pl-en">Action</span>
    spec = <span class="pl-ent">T</span>.simpleSpec performAction render




I don't know what the hell props are. Some kind of React thing?





Thermite uses a cute abstraction for composing components.

The combined state of two components is the product of their states (Pair).

The combined actions are the sum of their individual actions (Either).

compose ()

A Lens (and more generally an Optic) is a first-class setter and getter. Setters and getters are functions. In functional programming you pass those around. I think if you squint right they are also a bit like pointers. Setters and getters are kind of like a wrapper around a raw pointer too. Pointers are clearly data that can be passed around that holds the potential for both reading and writing data.

So a Lens let's you flexibly describe how you are embedding your component  inside on another.



What I said before about performAction was a total lie. You might expect it to have the type signature

action -> state -> state

but unfortunately it is not so simple. Actually performAction returns a CoRoutine. The reason is because a very common use case is for the browser to need to send off a request to a server and get some more info. Once it has that, it can. There is an easy way to lift a simple performAction of the form action -> state -> state into this more complicated thing, although it looks very scary and frankly clutters up the code. You can train your eye to just overlook it.

Look at the actual source. It's small. That must mean it's simple, right?

https://github.com/purescript-contrib/purescript-coroutines

There are different styles of coroutines. Just like Lens, it is a very scary datatype with up to 4 type parameters, i o m a. A piece of a pipeline can take an input i and output a type o while performing an effect monad m and finally returning a type a.

In a python generator, the yield statement would be given o and a final return statement would be given a.



CoRoutines come in different styles.

There are sources, sinks, transformers. transformers come in a couple flavors depending on the subtle difference of whtehr they first await a value or yield one.

However, it is useful to consider that you may want to perform effects at every stage of the coroutine, like printing to the console every time a number comes on through. That is why we need FreeT.

Producer o m Unit

type Co = FreeT

Oy Vey. Who ordered THAT? So FreeT is the Free Monad Transformer.

FreeT takes a functor f and returns a monad transformer that will slap the free monad corresponding to the command structure f on your monad stack. The choice of different f makes the different kinds of coroutines.

data Emit o next = Emit o next  is a reasonable looking command if you're used to such things. This thing is basically the functor that generates a list under Free and a list is a reasonable producer of a sequence of values

EffectList m a result = Cons a (m (EffectList m a))| Nil result



data Await a next = Await (a -> next)

await = liftFreeT (Await id)

via currying this is basically [a]->result














