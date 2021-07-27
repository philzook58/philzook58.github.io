---
author: Philip Zucker
date: 2021-07-27
layout: post
title: Replace Your Friends with a Markov Chain Slackbot
---

TL;DR <https://github.com/perciplex/new-friend> This is a slackbot that can be trained on your slack history to emulate your friends and coworkers to great amusement for all. 

You should check out Ben's blog post which is much more in depth with pretty diagrams <http://blog.benwiener.com/programming/2021/07/10/new-friend.html> See? 
![](http://blog.benwiener.com/assets/img/2021/07/convo_case.svg)

My friends and I have a side gig LLC called [Perciplex](https://perciplex.com/) that we've had for a few years. We spent a lot of time working on a project called [RaaS](https://raas.perciplex.com/) (on and off for over a year), which really went over like a lead balloon. I should make a write-up on the interesting bits of that.

After that, we wanted to get into breezier projects. So here's our first one.
We've had a slack for our friend group long enough that the word count of each individual can be in the 100,000 word count. We thought it would be fun for a bizarro robot channel to show up one day.

Originally we planned to take a stab at using recurrent neural networks. We got up and running doing that and while we were at it we tried out <deepnote.com> as a collaborative. It worked well enough that it was memorizing sentences. 

But then we took a step back to try the simpler approach, a simple markov chain model. We used this library <https://github.com/jsvine/markovify> which if you look at the contents of is not even that complicated. In essence, you collect a count of how many times a words follows it's previous words. You can pretty easily build this sort of thing yourself. <https://sookocheff.com/post/nlp/ngram-modeling-with-markov-chains/>

To sort of trick the markov chain to emulate a conversation, we tupled together the actual word and the user who spoke it as a "pseudo-word". We also added special "__SEND__" tokens. You can see that here <https://github.com/perciplex/new-friend/blob/f73dba011bc589c0ba825b92a4e6460fa28e0f26/new_friend/bot.py#L85>

Good stuff.








