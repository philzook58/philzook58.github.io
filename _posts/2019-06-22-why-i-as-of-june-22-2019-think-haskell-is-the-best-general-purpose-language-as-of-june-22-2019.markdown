---
author: philzook58
comments: true
date: 2019-06-22 23:23:17+00:00
layout: post
link: https://www.philipzucker.com/why-i-as-of-june-22-2019-think-haskell-is-the-best-general-purpose-language-as-of-june-22-2019/
slug: why-i-as-of-june-22-2019-think-haskell-is-the-best-general-purpose-language-as-of-june-22-2019
title: Why I (as of June 22 2019) think Haskell is the best general purpose language
  (as of June 22 2019)
wordpress_id: 2099
categories:
- Haskell
tags:
- haskell
---




Me and my close friends have been interested in starting a project together and I suggested we use Haskell. I do not think the suggestion was received well or perhaps in seriousness. I have a tendency to joke about almost everything and have put forward that we use many interesting but not practical languages in the same tone that I suggest Haskell. This was a tactical mistake. I find myself in despair at the idea I can't convince my personal friends, who are curious and intellectual people, to use Haskell on a fresh start web project we have complete control over. What hope do I have in the world at large? This brain dump post is meant for them. My suggestion to use Haskell is not _just _me being an asshole, although that does make it more fun for me. I will now try to explain in all seriousness and in all the honesty that I can muster what my opinions on languages are and why I have them.







Pragmatically can you start a new project using a language you don't know? This is a problem. A project always has some intrinsic difficulty. Not all projects will survive an extra layer of unnecessary speedbump. But when and how are you supposed to learn new languages? Never is one answer. I disagree with this answer. In this case we have the leg up that I do know Haskell. Perhaps this is a downside in that it will be extra frustrating? It is also easy for me to ask, as using Haskell is not a burden for me, I have already sunk the cost, but a massive learning burden for others.







Is Haskell actually practical for a web application? Short answer: yes. Expect pain though. If your web application is so simple you could rip it out in 100 lines of python, this is such a simple project that it is a good opportunity to learn something new. If it will become large and complex, then I believe Haskell does shine, keeping complexity under control. I base this upon the professional experience making a web application using a Haskell-Purescript stack. For honesty, it wasn't all good. I recall ripping my hair out threading shit through monad stacks to where it need to go. Yet on the whole, it kept the project sane. I also believe this based on the word of mouth that I believe but could be just cultish ramblings.







I believe that truly dominating properties of Haskell appear in large complex projects. This is difficult to prove in any other way except empirically and the experiments will be so wildly uncontrolled in terms of the project and people involved that no conclusions can truly be drawn. And yet I have faith, and think that personal experience validates this opinion to myself at least. We have to live this life even though truth does not exist. Choices and opinions must be made.







For programs that are going to be a single manageable file and written in one night, it doesn't matter much what you use in terms of being choked on your own code. At this scale, I still think Haskell is enjoyable and interesting though. Haskell was my doorway into the world of computer science as I now understand it. I hope there are more doorways.







Things about me that may be different from you. Decide for yourself if these aspects of me make our opinions fundamentally incompatible.







  * I do have a talent and a like for practically oriented mathematical topics (computational methods, linear algebra, formal methods, calculus, geometric algebra, projective geometry, optimization, etc.). I actually have very little taste at all for mathematical topics that I see no purpose to. 
  * I do have some desire and taste for esoterica for its own purpose. I cannot exactly characterize what makes some topics acceptable to me and others not. 
  * A hard learning curve is not necessarily a downside for me. I enjoy the challenge if it is overcomable and worth it on the other side.
  * I like weird and different. That is a positive for me, but a negative for many. I might just be a millennial hipster idiot.
  * I would LOVE to find a language I think is better than Haskell. I would LOVE to abandon Haskell. Perhaps this already makes me odd. Perhaps  I think many people don't consider the differences between languages to be worth making the switch and the wasted knowledge. The people with this opinion may or may not have tried enough languages. 
  * I have "drank the koolaid". I do read what comes out of the Haskell and functional programming community and have a tendency to believe things without strong empirical backing.
  * I have been more deeply entwined with Haskell than any other language. Perhaps if I had reached a level of familiarity in another language I'd be as fervent about that one? I don't believe this is the case.
  * While I desire performance, I consciously curb this desire. I am strongly in favor of cleanly written, clear, principled code. This is of course a weighted judgement. I will probably use a 100x performance gain for a 2x decrease in clarity or reusability. This is a result of the problem domains and scale that have interested me in the past and that I anticipate in the future. I STRONGLY believe the world at large over values performance at the expense of other good qualities of code. Or at least over optimizes early.






### A Biased List of Pros and Cons 







What do I find bad about C++.







  * The feature set is huge and difficult to understand
  * Extreme amounts of legacy features that will be even recommended if you read legacy documentation. Kitchen sink.
  * The language appears to be almost entirely built out of footguns.
  * The syntax is too verbose.
  * I have a distaste for mutation.
  * I have a distaste for object oriented programming






What do I find good about C++







  * It is commonly used. Large community.
  * It is possible for it to be very fast
  * Kitchen Sink. You can find almost any feature you want here.
  * The high level goals of the mind-leaders sound good.
  * Very interesting projects are written in C++. HPC things. Scientific computation.
  * Template metaprogramming seems very powerful, but arcane.






What I find bad about Java







  * The syntax puts me off as being incredibly verbose
  * Extreme object oriented focus
  * Corporate/Enterprise feel. I am an iconoclast and see myself as a reasonable but slightly rebellious character. Java in my mind brings images of cubicles and white walls. Perhaps this is not fair.






What do I find good about Java







  * ?






I'm joking. Sorry Java. But I also kind of mean it. Yes, there are positive aspects to Java.







What I like about python







  * Very commonly used and understood. Perhaps the lingua franca
  * Incredible library ecosystem
  * Numpy and scipy in particular are marvels of the modern age.
  * Syntax is basically imperative pseudo-code
  * I am personally very familiar with it
  * python is the easiest to use language I know.






What I dislike about python







  * Python has no natural tendency for correctness due to the free wheeling dynamically typed character. This is patched up with testing, opt-in type systems.
  * I don't know how to grow as a pythonista. The skill curve flattens out. For some this may be a positive. 
  * The main way of building new data types is the class system. I think this is ungainly, overly verbose, and not always a good conceptual fit. 
  * Despite being among the most succinct of common imperative languages, I still think it ends up being too verbose.
  * It is slow. This is a negative, although not high on my priorities.






What is bad about Haskell







  * Very difficult learning curve. Let's get real. Haskell is a very confusing programming language to get started in for common programming tasks.
  * functional programming is weirder than imperative programming.
  * The monad paradigm, even once learned is ungainly. Tracking multiple effects is a pain that does not exist in most languages.
  * The pain is up front. It is easy to get a sketch of what you want ripped out in python faster than in Haskell (for me). If you want a web server, command line tool, optimization problem, curve fitter, I can rip all of these out faster in python than I can in Haskell.  As a psychological thing, this feels awful. For a small scale project, unless toying with Haskell itself or one of its domain expertises like implementing DSLs, python is the easier and correct choice. Python is a scripting language. I'd make the switch at two screens worth of code.
  * I think laziness is confusing and easy to shoot yourself with.
  * Haskell is not the fastest language, although faster than python.
  * Concern for there not being jobs and interestingly on the converse side, no people to hire. There is a catch-22 there. There is a set of people that would KILL for a Haskell job.
  * There are vocal smug assholes who use Haskell and push it. I am smug, I hope only mildly an asshole.






What I find good about Haskell







  * The number one reason is that there is something ephemeral that I just like. I am not naturally inclined to analyze such things. When I like a movie or don't like it, it just happens, and if forced to explain why, I'll bullshit.
  * Errors and bugs are to a shocking degree caught at compile time. More than any other language I have experience with does Haskell code run correctly without hidden bugs if it compiles. I am not claiming this is absolute but it is all the more incredible the degree to which it is true since it didn't literally have to be this way. I have done major rewiring of a data structure in a project. The compiler guided my hand to exactly the positions that needed to be adjusted. Could C++ do this? Yes, to some degree. I believe that the tendencies of C++ programming make it less satisfactory on this point.
  * Types are an incredible design tool. I find designing the types of my program to be an extremely enjoyable and helpful activity. Much more so than box and wire class and interface diagrams. A good function name and a type signature basically entirely constrains the behavior of a function. Types can be quickly and completely be given to the compiler and machine enforced.
  * The pain that Monads cause are pains you should be feeling. They are the pain of explicitness which I 70% choose over the pain of not knowing what the fuck a function might do, and not enabling the compiler to enforce that. If something is capable of mutating state, it should say so in goddamn huge purple letters.
  * Haskell is more than fast enough. It isn't that even people don't care. The Haskell community at large cares a lot more for performance than I do, and I reap the dividends. The people in charge of the compiler and the main libraries are goddamn wizards who's work I get to benefit from. This is true of all languages perhaps.  
  * Laziness is very cool. At the beginning I thought it was INCREDIBLY awesome and inconceivable that I could manipulate an infinite list.
  * The way of specifying new data types is so succinct and so incredible. Pattern matching is SO GODDAMN good for some tasks.
  * Haskell has a paradigm of small combinators. It is common to build a sequence of very small natural functions for the domain and then build larger and larger things out of them. This is good for reusability and conceptual clearness.
  * Extreme preference for Immutability. As part of keeping what you must keep in your head or remember small while programming, immutability is an insane win. You think you know what you want now. You know you could just tweak this variable here, make a special variable over here. You can reason about how to make this all work and be correct now. You will not in a month. Your coworkers will mess it all up too.
  * Haskell code is generic by default. This allows the same code to be reused in many situations
  * The standard typeclass hierarchy is extremely well thought out and powerful. To some degree it is unnecessary in other languages. The difference between Functor, Applicative, Monad, and Traversable makes little sense in languages with unconstrained mutations and effects.
  * Haskell paradigms are inspired by mathematics, and I have great faith in mathematics. The concepts behind Haskell feel closer to discoveries rather than inventions. Imperative programming speaks in a language formed for the accidental nature of the machines we have. Functional programming is a language closer to mathematics, which I believe is closer to how the human mind works, and closer to what the problem at hand actually is.
  * Complexity scales. It is my belief, perhaps unverified, that as a project grows larger, the insane miserable churn and mental overhead grows slower in a Haskell project than in other languages. I do not have strong empirical evidence to this assertion. Word of mouth (of Haskellers). 
  * The ceiling on Haskell is extremely high. You can continue to learn and get better, gaining more and more power. I do not currently see the end of this.
  * When I do reach for some new library, I am very often impressed by how thoughtfully built it is. Haskell itself is INCREDIBLY thoughtfully built.
  * The haskell community is very excited and they have many things to teach. There are many Haskellers out there who are very welcoming, kind, and intelligent.
  * Haskell does have some cache. I am not immune to wanting to seem smart. If the world thought that only idiots use Haskell, that would offput me some. That the world things that only impractical ivory tower smug weenies use Haskell does offput me, although I perhaps embrace it belligerently.
  * The Haskell library ecosystem is strong. Less strong than python, but much better than some of the other languages that intrigue my eye. There is functionality somewhere for most common tasks.
  * Haskell is used industrially. I live in an echo chamber, but by and large the industrial users of Haskell sing its praises.






For context, this is my programming journey:







I first learned BASIC in middle school. I wrote a computer game in Visual Basic. I toyed with the TI-83. I went to a summer camp in high school where I learned the extreme rudiments of C++. Did a small web business with some friends. Did really bad work with big dreams. I took a fairly poor Java course in high school. I learned MATLAB in college.  I doinked around with Arduino level C projects. I learned python in grad school I think. I think I got far more proficient at python than any other language before. At this point, I was on board for object oriented programming, albeit not at a deep level (design patterns or ilk), just as light organizational principle. Did some Android projects, really didn't like Java there.  Did a small business with my friend and got deep in Javascript. As our web application got bigger, this really start to hurt. Errors all over the place. Unknown junk in objects. Who has access to what? We tried our darndest to read and follow best practices as we could find them, but it felt like we sinking in quicksand. More and more effort for more and more bugs and less and less progress. It was around this era that I first even heard of Haskell. I was intrigued immediately for some reason, maybe for just how weird it was. It took probably 2 years of forgetting about it and going back to tutorials every 6 months. I didn't necessarily KNOW that this was a thing that I wanted, I just found it interesting. Currently I am fairly proficient at some things in Haskell (unfortunately I am more proficient at esoterica than more practical things). I have had a professional job writing Haskell, and it seems like my like of Haskell is working out very well for me professionally. Passion in all forms is powerful. 







My history may not be as convincing as someone who spent 20 years as a professional C++ dev and then switched, but I have at least experienced different paradigms and languages and found Haskell the most to my liking.







### Random Thoughts







I am now trying to push myself into comfort in Julia, Rust, Agda, Coq, OCaml, all languages I feel show promise for different reasons. To my knowledge Haskell is a better choice than these as a general purpose tool for pragmatic reasons. Haskell's library ecosystem is strong and performance is good. These are points against agda and coq. Julia has a focus on scientific programming.







Rust might be a good compromise. I consider it a trojan horse for useful programming language features that I associate with functional languages. It claims to performance and being an acceptable systems level language, which appeals to some. The syntax does not scare anyone off. The library ecosystem seems good and the community strong. I did find myself missing Haskell features in Rust though, am personally much less familiar with it. I think the design of Rust weights more to performance than is warranted in most applications and has less descriptive and abstraction power than Haskell, qualities that I prioritize. This opinion is not strongly held.







What makes Haskells types any better or worse than C? At the beginning many of the features of Haskell seem like magic. But as time has worn on, I can see how the features can be emulated with just some slight syntactic and conceptual overhead in other languages. This slight overhead is enough though.  A language is more than just it's syntax. It is also its idioms. It is also they way it makes people think. Language is almost a prerequisite for thought. You cannot even conceive of the ways there are to express yourself before learning.







What exactly makes a language "good"? This is a question poorly phrased enough to have no answer. Excel can be an excellent language for many tasks. Easy to learn. Very powerful. Yet, it is not considered a good general purpose programming language. Library ecosystem is extremely important. Specialized languages are often the best choice for special problem domains, at the expense of learning them, or eventually finding incompatibility of what you want from what they designed for.







What makes abstractions "good". Why do I have queasiness about object oriented-programmming. Java, I think basically. I, overeagerly have gone down the road of trying to design deep subclass hierarchies, which is not OO at it's best. Zebra is a Quadruped is an Animal is Alive kind of stuff. I believe object oriented in an interesting principle. I hear about SmallTalk and Common Lisp doing object oriented right and I am duly intrigued. There has been some recent work in Haskell about how to do objects in a way aesthetically compatible with Haskell. I think object oriented has been over used and abused. I think it is a poor conceptual fit for many situations. I think it tends to make non reusable code. I think the form that it takes in C++ and Java development is arcane horseshit.







I deserve almost no opinion about Java or C++, having not done sufficient that much in them. Yet, I must state my opinions, take them as you will, for I do in fact hold them strongly. I have worked on a network simulator and a robotics framework in C++, but begrudgingly. I have done a very small amount of Java development for a personal project and some Processing sketches. My coworker was a 10 year professional Java dev before switching to Scala then Haskell. He despises Java now. Highly anecdotal, and he is a similar iconoclastic character like me. Nevertheless, this also informs my opinion. I have been reading Bjarne Stroustrup's book (his stated goals and what he claims C++ achieves are admirable and one can't argue he hasn't changed the world) and actually find C++ rather interesting, especially in the sense that many projects that I find interesting are written in C++, I just don't want to myself work in the language. 







Haskell love:








https://www.reddit.com/r/haskell/comments/6snhth/what_is_great_about_haskell/









https://www.reddit.com/r/haskell/comments/6segl8/why_should_anyone_use_haskell/








Haskell Criticism (perhaps warranted)







[https://news.ycombinator.com/item?id=17114308](https://news.ycombinator.com/item?id=17114308) Ah Hacker News. Always a sunny worldview.







[https://medium.com/@snoyjerk/least-favorite-thing-about-haskal-ef8f80f30733](https://medium.com/@snoyjerk/least-favorite-thing-about-haskal-ef8f80f30733)







Hacker news discussion of this post:







[https://news.ycombinator.com/item?id=20258218#20271511](https://news.ycombinator.com/item?id=20258218#20271511)



