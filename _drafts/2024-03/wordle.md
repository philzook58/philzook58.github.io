
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

```python
guesses = "SLATE                         "

sols = [
    "SCARY",
    "EQUAL",
    "CHOKE",
    "MOVER",
    "REACT",
    "BETEL",
    "LINEN",
    "AMITY",
    "CEDAR",
    "FELLA",
    "COVEN",
    "SOWER",
    "EERIE",
    "AGILE",
    "FOCAL",
    "GAILY",
    "STARK",
    "THESE",
    "CHURN",
    "SCONE",
    "LIPID",
    "STYLE",
    "APPLE",
    "MAXIM",
    "DECRY",
    "EDICT",
    "ONSET",
    "SKIMP",
    "AGONY",
    "CROUP",
]
color = [
    "G",
    "G",
    "G",
    "G",
    "G",
    "G",
    "G",
    "G",
    "G",
    "G",
    "G",
    "G",
    "G",
    "G",
    "B",
    "G",
    "G",
    "G",
    "G",
    "G",
    "G",
    "B",
    "B",
    "B",
    "G",
    "B",
    "G",
    "G",
    "G",
    "G",
]


gamestate = {
    "encWords": "PUTIT HERE",
    "signature": "SIGNATURE HERE",
}


def do_guess(guesses):
    req = f"""curl 'https://mythstoryhunt.world/api/puzzle/do-you-like-wordle/makeguess' \
    -H 'authority: mythstoryhunt.world' \
    -H 'accept: */*' \
    -H 'accept-language: en-US,en;q=0.9' \
    -H 'content-type: multipart/form-data; boundary=----WebKitFormBoundary' \
    -H 'cookie: sessionid=-------------------------- \
    -H 'origin: https://mythstoryhunt.world' \
    -H 'referer: https://mythstoryhunt.world/puzzles/do-you-like-wordle' \
    -H 'sec-ch-ua: "Not_A Brand";v="8", "Chromium";v="120", "Google Chrome";v="120"' \
    -H 'sec-ch-ua-mobile: ?0' \
    -H 'sec-ch-ua-platform: "Linux"' \
    -H 'sec-fetch-dest: empty' \
    -H 'sec-fetch-mode: cors' \
    -H 'sec-fetch-site: same-origin' \
    -H 'user-agent: Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36' \
    --data-raw $'------WebKitFormBoundary\r\nContent-Disposition: form-data; name="encWords"\r\n\r\n{gamestate["encWords"]}\r\n------WebKitFormBoundary\r\nContent-Disposition: form-data; name="signature"\r\n\r\n{gamestate["signature"]}\r\n------WebKitFormBoundary3RRD\r\nContent-Disposition: form-data; name="guesses"\r\n\r\n{guesses}\r\n------WebKitFormBoundary--\r\n' \
    --compressed"""
    import subprocess

    response = subprocess.check_output(req, shell=True)
    # import os

    # response = os.system(req)
    # print(response)
    import json

    # print(response)
    resp = json.loads(response)
    print(resp)
    print("topBar", resp["data"]["topBar"])
    color.append(resp["data"]["topBar"].strip())
    games = [
        resp["data"]["gameStates"][game * 30 : (game + 1) * 30] for game in range(30)
    ]
    games = [[game[i * 5 : (i + 1) * 5] for i in range(6)] for game in games]
    return games


words = []


def make_guess(game, guess):
    guess = guess + " " * 25
    res = do_guess(guess)
    return res[game][0]


from english_words import get_english_words_set

web2lowerset = get_english_words_set(["web2"], lower=True)
wordlist = [word.upper() for word in web2lowerset if len(word) == 5]
wordlist.append("DELLA")
wordlist.append("BELLA")
wordlist.append("PELLA")
wordlist.append("FELLA")
wordlist.extend(
    ["COVEN", "JOVEN", "BOVEN", "ROVEN", "WOVEN", "HOVEN", "DOVEN", "LIPID"]
)
import random


def solve(gamenum):
    sol = [None] * 5
    guess = "SLATE"
    words = wordlist.copy()
    doesnt = set()
    has = set()
    while True:
        print(guess)
        result = make_guess(gamenum, guess)
        print(result)
        if result == "GGGGG":
            return guess
        if result == "RRRRR":
            # words = words[1:]
            # guess = words[0]
            words.remove(guess)
            guess = random.choice(words)
            continue
        for i in range(5):
            if result[i] == "G":
                sol[i] = guess[i]
            elif result[i] == "Y":
                has.add(guess[i])
            elif result[i] == " ":
                pass  # doesnt.add(guess[i])
                # breakpoint()
        print(f"words: {len(words)} has: {has}, doesnt: {doesnt}, sol: {sol}")
        words = [word for word in words if has.issubset(word)]
        # words = [word for word in words if len(doesnt.intersection(word)) == 0]
        words = [
            word
            for word in words
            if all(k == w for k, w in zip(sol, word) if k is not None)
        ]
        guess = random.choice(words)


"""
for gamenum in range(len(sols), 30):
    sol = solve(gamenum)
    sols.append(sol)
    print(sols)
"""
# print(solve(4))
print(len(sols))

print(list(sol for sol, col in zip(sols, color) if col == "B"))

# for n, sol in enumerate(sols):
#    do_guess(sol + " " * 25)
#    print(color)
color = []
for n in range(6):
    guess = "SHARE" * n + "SCARY" + " " * 5 * (5 - n)
    do_guess(guess)
    print(color)


[
    ("SCARY", "G"),
    ("EQUAL", "G"),
    ("CHOKE", "G"),
    ("MOVER", "G"),
    ("REACT", "G"),
    ("BETEL", "G"),
    ("LINEN", "G"),
    ("AMITY", "G"),
    ("CEDAR", "G"),
    ("FELLA", "G"),
    ("COVEN", "G"),
    ("SOWER", "G"),
    ("EERIE", "G"),
    ("AGILE", "G"),
    ("FOCAL", "B"),
    ("GAILY", "G"),
    ("STARK", "G"),
    ("THESE", "G"),
    ("CHURN", "G"),
    ("SCONE", "G"),
    ("LIPID", "G"),
    ("STYLE", "B"),
    ("APPLE", "B"),
    ("MAXIM", "B"),
    ("DECRY", "G"),
    ("EDICT", "B"),
    ("ONSET", "G"),
    ("SKIMP", "G"),
    ("AGONY", "G"),
    ("CROUP", "G"),
]
```
