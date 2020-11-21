---
author: philzook58
comments: true
date: 2017-12-06 13:29:37+00:00
layout: post
link: https://www.philipzucker.com/?p=933
published: false
slug: Reification and Reflection
title: Reification and Reflection
wordpress_id: 933
---

Reflection is some kind of black magic. Here's the references

https://www.schoolofhaskell.com/user/thoughtpolice/using-reflection

https://hackage.haskell.org/package/reflection

http://okmij.org/ftp/Haskell/tr-15-04.pdf

The typeclass proposition (Reifies s a) is the statement that s is a type that corresponds in some way to a value of type a.

The typeclass has a member variable reflect which proves that fact. When you call that function with value of the type s (basically) it returns the value.

Now to explain that basically. The Proxy data type is a way of giving types that don't really have values a dummy value. So reflect actually takes a  (Proxy :: Proxy s) and returns the a.

With DataKinds, analogous type level constructions get built. I don't think this is necessarily connected to this story. The type s stays abstract. It is just a name with the only property that it reifies a. I don't know how to turn a value into it's datakind. Maybe you can't. Probably you can't. That would take you into dependent types. You can turn a datakind into it's value though. The only way to turn a value into anything other than an abstract type is to be able to know that value at compile time. Which maybe you could do. Also if they value came from converting from a type in the first place.

https://hackage.haskell.org/package/singletons

Singletons are a way of converting DataKind Typelevel stuff down to the value level. The Typelevel singletons also let us constrain types.

This is all an orthogonal story. Except for the question of how do we traverse from values to types to kinds and typeclasses









reify builds a typelevel tag to that value. Its implementation goes a little outside Haskell land, just like ST or IO, but you can use it safely and consistently. You give it the value and the continuation that will take the proxy.

then inside the continuation you can reflect that value out of the proxy.

Why not just use Reader? That is the standard Haskell way to weave some configuration value through. I think the point is aesthetics? The paper states that writing everything in monadic style is unwieldy.

https://www.reddit.com/r/haskell/comments/3hw90k/what_is_the_reflection_package_for/



So Ed Kmett's answer is about a bunch of performance stuff.

https://github.com/ekmett/reflection/blob/master/examples/Monoid.hs

It also let's you dynamically build typeclasses. Typeclasses convert to dictionaries at runtime. You can build a schema instance on how to convert a particular dictionary type to that typeclass. A type that wants to have a dynamically bindable dictionary needs to have a type parameter that tags it to that dictionary (M s a)



Given is a simplified Reifies where you don't pass around the proxy. It figures it out by matching types.

=> is kind of like ->

It resolves to an array with a dictionary on the left side at runtime

So with Reader = (->) a we can kind of convert it to

Given a =>

and now you can grab the value with "given". In order to actually run the function you need to use "give" which has the appropriate type constraint.



The constraints package

http://neocontra.blogspot.com/2013/06/controlcategory-now-with-kind.html




