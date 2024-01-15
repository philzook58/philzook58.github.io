
I've been thinking about how to teach a couple of people about programming. I'm into it right? I think python is basically the best first language in that there are lots of resources.

For the MIT puzzle hunt this year, there was an odd Wordle game. It had 30 synachronized wordles. I went into the dev console and realized that the thing is totally stateless with rspect to the server. It sends and entire state string and your current choices, so actually you can reset the thing back to the first move. The board state is encoded in some way (which seems fishy. maybe it's easy to decrypt).

I tried looking up just a wordle solving library and couldn't find one. The blog posts seemed complicated.

So I implemented a very simple suboptimal worlde solver. Basically it just prunes the database for currently compatible words and picks a random one.
I think picking a random one is kind of nice because a random one will tend to have common letters, which is a reasonable strategy to gain information.

Some smarter strategies might involve reinforcement learning or some kind of lookahead search.

My dictionary and the servers did not match, which is a problem. It had solutions I did not and vice versa. Bummer.

It was surprisingly hard to figure out what word dicitonary to use.
First filter to 5 letter words.

An even easier puzzle is spelling bee.
