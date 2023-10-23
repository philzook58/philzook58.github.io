

# How to search for shit

The power of magic words
Reverse citations
Dig down to a highly cited paper and dig up
Look at common authors

# How to understand
Read many things shallowly. 5 books at once. Keeps it fresh. You'll notice the important commonalities
Keep a textfile open
Write an explanation on your blog and get precious doots
Break down, concretify and simplify to a ridiculous extent
What homework would you assign? Do it. Understanding is in the hands.

[Read stuff backwards, exercises first](https://twitter.com/sigfpe/status/1467568480241152001?s=20)


https://news.ycombinator.com/item?id=28953781 how to learn the asterisk method
active learning
- copy out. rote learning is good
- gotta load stuff up to the brain
- 

#### code base splelunking
- Build it. Try verbose mode. Try to kind of pay attention to the stream of things flying by
- Run it. Run the examples
- Look at tests
- Look at build files. They may implicitly provide a hierarchy
- Look top down or bottom up. If there is an output, something prints it. There is probably a main


- Try trivial modifications. Adding a case to some data type for example.

- colin - use gdb and just watch it go.

[Ask HN: What are the ways you go about getting comfortable with a new codebase?](https://news.ycombinator.com/item?id=32365660)
- Try to profile it. You might also be a hero for doing so.


# Blogging

https://www.gwern.net/
Dan luu
Dan piponi


It's hard to pick links. Some of REALLY good, but it's hard to denote that. This is why link dumps aren't that useful. Lack of emphasis.

Ctrl+Shift+V puts in markdown render mode.
"markdown shortcuts" auto generates table of contents
Go into .vscode/jeepshen... /src/share.js to add new languages. Not ideal
Also executorMap in package.json. I re aliased python to python3

Maybe what I want is shebangs  `#! c++ /tmp/foo -o /tmp/a.out && /tmp/a.out`? Sometimes I want to add command line flags. Then I could use whatever highlighting I want. It would be better to have a hotkey to do this.

```python
print("hello world")
```
```ocaml
let () = print_endline "hello world"
```
```julia
print("hi")
```
```bash
echo hellow
```
```c
#include <stdio.h>
int main(){
    puts("foo");
}
```
```souffle
.decl foo(x : number)
foo(3).
.output foo(IO=stdout)
```

```

npm install –g vsce
vsce package
```
# Is a PhD Good
My opinions are informed by my history and background, as anyone's is.

https://news.ycombinator.com/item?id=26413343 - that nautolius article "you quit"


If you're going to be white and male, it helps to be jewish.

# Publish or Blog?
Something I struggle with is that I feel a desire to publish or a guilt for not doing so.

A part of me gets belggerent in defense. The world is filled with garbage research. Everyone has to scream at that top of their lungs or chase papers. My advisor would take me aside and give a little speech bemoaning the state of te publishing world. I have escaped that.

The style of research articles is a certain kind of professional. The incentive is to demonstrate sufficient erudition of difficulty of the result to get the paper published, not persay demonstrating how ultimately simple the thing done was in hindsight.

Does 



Ok, but pulling back into attack myself mode, why don't I publish? It's because I don't have the skills or ideas of sufficient worth or complexity to publish them.

I have a pretty bad attention span. Sticking to a project for months or years is excruciating for me. I'd much rather an idea to a proof of concept, mildly edit a blog post, dump it out and receive my external validation from twitter thank you very much. I fear this may end up being to some degree cookie licking, which is also a serious problem for the research community

I also do believe in fail fast. You do not know which of your ideas is something that will land in other people. Very fast spray is possibly a good strategy. On the other hand, the ideas might ned a fai shak

To some degree, getting a blog post out is a way for m to let go of an idea I can't stop fixating on. It is the worst that I have piles and piles of projects that I have gotten the meat out of but never sealed off enough to make them go away from my mind.


You really can sort of wander through life and wake up in 20 years and not have done things you feel you're capable of.
This torments some people.


# I hate everyone else's Macros
But I love mine.

## What is the whole thing of programming tricks
It's to abuse your host languages features.
To avoid deeply embedding DSLs


# How did I get here

# What is practical / prgamatic

Should I be using formal methods?

If no one in your industry uses it, and you find it uninteresting, don't do it. Life is too short.
If people in your industry are interested, and you've actually investigated it and think it will make your life hell, fight it tooth and nail.


People who work in the field want you to think so. It is in their best interested in terms of prestige,
Just because they use big fancy words and opine about the philosophical beauty 
Just because it is in their best interest does not mean they are wrong.

# Proxies
Something I thought was very interesting from the machine learning course was to be careful of proxy/surrogate goals. At a certain point, you, or the alorithm for your team ends up over optimizing to the proxy. Every metric is gamed eventually.

There is only as much a point to optimizing to a goal to the degree it is an accurate representation of what you're actually trying to do.

From a different tact. operations research like MIP and CSP are a bit silly. The difference between a fast heuristic for solving these models and an exact opitmal solution may be irrelevant for applications. And the exact solution has a tendency to game the model in such a way that is not robust to model inaccuracy.

This also occurs in compilers. We think we have a rough model of what a cpu cares about. Use less registers, don't touch memory unless you have to, use less instructions. Then finer grained models talk about dependencies between instructions affecting instruction level parallelsim, or cycle counts or resource usage of individual instructions. But in the end of the day these models are fairly coarse. Spending a _ton_ of compilation time may _never_ be worth it.

This is not to say proxies are not extremely useful. The actual objectives of life are ultimately unknowable. But even if you think the goal is money the corporation makes, the connection between the decisions you can make or even what decision are available is not set in stone and _also_ unknowable. Proxies are a best effort attempt here to model what seem like reasonable effects.

Sometimes we make proxies of proxies. We know we have a better model, but simplify it for analytic reasons or ease of measurement. This is all valid. We just need to remain aware of what we've done.

- Training set is proxy for real world use
- engineering Models are proxy for physical performance
- LoC or pull requests or issues closed as engineering output. 


# Managing Time
Pomodoro
GTD

# How to Manage / Lead
Project lead
Focus blocks - https://frankgrecojr.medium.com/focus-time-saved-me-from-burnout-88cff1829276 hard rule set out tme
1 on 1 meetings