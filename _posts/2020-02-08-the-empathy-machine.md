---
author: Philip Zucker
date: 2021-02-08
layout: post
title: The Empathy Machine
tags:
- javascript
- computer vision
- tensorflow
---

## [https://iamyouyouare.me/](https://iamyouyouare.me/)

An idea that has been kicking around for while is to create an augmented reality empathy machine. The idea is that we'd paste your face onto everyone else in sight, giving you some kind of empathic revelation. 

![](/assets/bobby_ben.gif)

It does feel odd, I'll admit. 

Will has kept the flame of this idea alive for years, but we finally got around to doing it. It's been fun. Much ice cream has been had.

It's now up on [https://iamyouyouare.me/](https://iamyouyouare.me/) and the code is at [https://github.com/Smung-Institute/empathy-machine](https://github.com/Smung-Institute/empathy-machine). The main bulk of the work is done by Tensorflow.js [Facemesh](https://github.com/tensorflow/tfjs-models/tree/master/facemesh), which was the starting point. It works pretty dang well, better than I could've hoped. The project has been pretty straightforward gluing together facemesh with a threejs overlay, figuring out web apis and such.

In addition to your own face, it can be fun to use famous faces or cartoon faces. I also advise taking a photo with you head tilted down or slightly to the side.

Usually as part of the physics departments art shows, Ben, Will, and I have done little toy techy art projects. I do not have a soul, which is why I can't bear just doing art for it's own sake. There has to be some technical challenge to it. I'm a sick man.
Anyhoo, previously projects that come to mind are the [laser table](https://hackaday.io/project/8556-laser-table)[Will's blog](https://willmaulbetsch.com/portfolio/laser-table/)  where people could cooperatively draw with a laser on a fluoruescent table over the web.
Another was was [Space Adventure Zone](https://willmaulbetsch.com/portfolio/orrey/) where will filled a room with AR tags so you could be space whales visiting earth on your phone.

[as god intended](https://twitter.com/SandMouth/status/1318354659707252736?s=20)