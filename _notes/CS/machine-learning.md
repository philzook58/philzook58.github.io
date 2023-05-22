---
layout: post
title: Machine Learning
---

- [Applications](#applications)
- [Data](#data)
- [Good Practice? What's the right word here](#good-practice-whats-the-right-word-here)
- [Supervised](#supervised)
  - [Linear in WHAT?](#linear-in-what)
  - [Nearest neighbor](#nearest-neighbor)
  - [SVM](#svm)
  - [Kernel](#kernel)
  - [decision trees](#decision-trees)
- [Unsupervised](#unsupervised)
- [Visualization](#visualization)
- [Learning Theory](#learning-theory)
- [Overfitting](#overfitting)
- [Bayesian Shit](#bayesian-shit)
  - [Regularization](#regularization)
- [Deep Learning](#deep-learning)
  - [Convolutional](#convolutional)
  - [Recurrent](#recurrent)
  - [tidbits](#tidbits)
- [Verification](#verification)
- [Famous Models](#famous-models)
    - [LoRA](#lora)
    - [Stable Diffusion](#stable-diffusion)
    - [Mixed Precision](#mixed-precision)
    - [prompt engineering](#prompt-engineering)
    - [Transformers](#transformers)
  - [Large Language Models](#large-language-models)
    - [Models](#models)
    - [Data sets](#data-sets)
    - [Openai](#openai)
    - [langchain](#langchain)
    - [Vector Databases](#vector-databases)
  - [Backprop Technqiues](#backprop-technqiues)
  - [Frameworks](#frameworks)
- [Hugging Face](#hugging-face)
    - [fastai](#fastai)
  - [Resources](#resources)
- [Reinforcement Learning](#reinforcement-learning)
- [Verification](#verification-1)
  - [Resources](#resources-1)
- [Old Reinforcement learning](#old-reinforcement-learning)


See also:
- Optimization

[ml for proofs bibliography](https://github.com/tlringer/ml-for-proofs)


# Applications
- Speech recognition
- Image recognition
- branch prediction
- phase transition recognition
- Dimensionality reduction?
- recommender systems
- Fluid sim accelerate
- system identification
- learning program invariants http://pranav-garg.com/papers/cav14.pdf https://www.cs.purdue.edu/homes/suresh/papers/pldi18.pdf

# Data
outliers


augmentation - sometimes you can apply trasnformations to the data in ways. For example rotating images if you want the answer to not depend on direction. Or adding noise if you want it to ignore noise. Warping.

In some problems it's nice that you can cripple your data and train it to undo the crippling
- colorizing images
- interpolating frames
- super resolution


# Good Practice? What's the right word here
Test and training sets
cross validation
data cleaning
meta parameter tuning
don't set auxiliary goals.

Reading training curves
debugging?

# Supervised

$$ \hat{y}_i = f(x_i; \theta) $$

Classification
discrete output

Regression - continous output

one hot encoding



## Linear in WHAT?
## Nearest neighbor
## SVM
## Kernel
## decision trees

# Unsupervised

PCA
k-means clustering
hierarchical clustering

dimsenionlaity reduction?

# Visualization
t-sne
umap

# Learning Theory
VC dimension

# Overfitting


bias variance

# Bayesian Shit
pyro pymc3
stan 
particle filters?
probalistic programming

## Regularization
[diffrax](https://twitter.com/PatrickKidger/status/1493239723497857025?s=20&t=vnpYi0b4BbBHdrISb_Kxfw) JAX powered differential equations.

# Deep Learning
https://github.com/AUTOMATIC1111/stable-diffusion-webui


## Convolutional

## Recurrent
lstm
gru
blowup problem / vanishing gradient

## tidbits
 Attention
 Capsule
 transformers

batch normalization

dropout
grokking? overfit and keep going. Sometimes it gets better later. Bizarre. Don't count on this. https://mathai-iclr.github.io/papers/papers/MATHAI_29_paper.pdf
autoencoders
GANs

graph neural networks?

transfer learning

# Verification
Adversarial examples

# Famous Models
word2vec
node2vec

code2vec

copilot


gato

wavenet
DALL-E
stable diffusion
midjourney

alexnet
vgg
alphafold
alpha zero / go
BERT

https://github.com/facebookresearch/segment-anything 
### LoRA
Low rank adaptation
https://arxiv.org/abs/2106.09685
But people are also using the technique on stable diffusion
[Using LoRA for Efficient Stable Diffusion Fine-Tuning](https://huggingface.co/blog/lora)

Lora let's you fine tune big models by injecting in small layers that are easier to train

PEFT parameter efficient fine tuning https://www.youtube.com/watch?v=YVU5wAA6Txo&ab_channel=code_your_own_AI

https://civitai.com/ people post their lora updates

https://twitter.com/rasbt/status/1642161887889567745 soft finetuning
prefix finetuning

[Fine-tuning 20B LLMs with RLHF on a 24GB consumer GPU](https://huggingface.co/blog/trl-peft)

### Stable Diffusion
https://www.fast.ai/posts/part2-2023.html course

inpainting
outpainting

### Mixed Precision
https://github.com/NVIDIA/apex
https://github.com/ggerganov/llama.cpp/issues/9
GPTQ quantization
### prompt engineering
https://www.promptingguide.ai/
Question answer format to give a couple examples
Start a conversation
See openai examples page
People use seperators to denote different sections. Weird.

Avoid impreciseness

chain of thought prompting https://arxiv.org/abs/2201.11903
### Transformers
## Large Language Models
https://openai.com/research/instruction-following instructgpt RLHF reinfrocement learning human feedback

alpaca https://crfm.stanford.edu/2023/03/13/alpaca.html llamma fine tuned. Make a bunch of examples. Make gpt3 build a dataset out of them, finetune llama on those answers


Emery berger is going ham. I think basically what he is doing is grabbing pertinent data and constructing a gpt prompt

[](https://huggingface.co/blog/stackllama)

langchain https://www.pinecone.io/learn/langchain-intro/
https://github.com/microsoft/semantic-kernel microsoft version of langchain?

https://github.com/unitaryai/detoxify detect toxix comments. I suppose you just need to detect if the output is mean and then you can block it. AI vs AI

https://bellard.org/ts_server/  text synth server fabrice bellard

https://www.emergentmind.com/
https://www.builder.io/blog/ai-shell

Chinchilla scaling - There is an amount of data and number of parameters that is compute optima

https://news.ycombinator.com/item?id=35483933 chatdbg, another gdb chatgpt integration

https://github.com/openai/tiktoken tokenizer BPE byte pair encoding https://platform.openai.com/tokenizer try out te tokenizer

https://github.com/openai/openai-cookbook open ai cookebook

[sentence transformers](https://www.sbert.net/) make embeddings easily?

"Pre-training" is the heavy lift huge datacetner part that produces raw gpt3 models or whatever. Weird terminology to call that pretraining

ICL - in context learning - running inferece. A set of examples in the prompt

[deep to long learning](https://news.ycombinator.com/item?id=35502187) Context length is important. It scales poorly

Perplexity - measurement of inaccuracy of model prediction on test set https://en.wikipedia.org/wiki/Perplexity

NLP - 
unigram model - probility of individual words
n-gram model - condtional probability of word window
### Models
https://vectara.com/top-large-language-models/ useful summary. Probaby will be outdate in a month

- gpt-3
- chatgpt
- llama https://news.ycombinator.com/item?id=35100086 llama weights leaked. 4 bt quantization. https://github.com/rustformers/llama-rs

- Bloom https://huggingface.co/bigscience/bloom
- eleuther gpt-j https://en.wikipedia.org/wiki/GPT-J https://www.width.ai/post/gpt-j-vs-gpt-3 https://github.com/EleutherAI/gpt-neox
- gpt4all - another lora finetuning of llama
- flan-t5 / flan-ul2 / t5-xxl
- PaLM

gpt-cerebras - the point it was trained efficiently, not that its good? https://news.ycombinator.com/item?id=35487846
claude https://www.anthropic.com/index/introducing-claude

rwkv https://github.com/BlinkDL/RWKV-LM https://news.ycombinator.com/item?id=35370357  https://github.com/saharNooby/rwkv.cpp

### Data sets
The Pile

### Openai 
```python
import openai

# list models
models = openai.Model.list()
#print(models)
# print the first model's id
print(models.data[0].id)

# create a completion
completion = openai.Completion.create(model="ada", prompt="Hello world")

# print the completion
print(completion.choices[0].text)
print(completion)
```

```bash
# list models
openai api models.list

# create a completion
openai api completions.create -m ada -p "Hello world"

# create a chat completion
openai api chat_completions.create -m gpt-3.5-turbo -g user "Hello world"

# generate images via DALL·E API
#openai api image.create -p "two dogs playing chess, cartoon" -n 1

# audio.transcribe
# audio.translate

```


Embeddings
https://www.buildt.ai/blog/3llmtricks embedding tricks. Hyde - predict answer from query, then use embedding of predicted answer

```python
import openai

# choose text to embed
text_string = "sample text"

# choose an embedding
model_id = "text-similarity-davinci-001"

# compute the embedding of the text
embedding = openai.Embedding.create(input=text_string, model=model_id)['data'][0]['embedding']
print(embedding)
```

### langchain

```python
from langchain.llms import OpenAI
llm = OpenAI(temperature=0.9) # hgh temprateur
text = "What would be a good company name for a company that makes colorful socks?"
print(llm(text))
```

```python
from langchain.prompts import PromptTemplate

prompt = PromptTemplate(
    input_variables=["product"],
    template="What is a good name for a company that makes {product}?",
)
print(prompt.format(product="colorful socks"))
```

https://github.com/Unstructured-IO/unstructured
### Vector Databases
Databases that include the abilitt to do fuzzy search for vectors (from embeddings)

Approximate nearest neighbor: [FAISS](https://github.com/facebookresearch/faiss),  https://github.com/spotify/annoy https://github.com/nmslib/hnswlib/

- Pinecone
- Milvus
- Weaviate
- Qdrant

[missing where clause](https://www.pinecone.io/learn/vector-search-filtering/), pre vs post filtering

sqlite vector search
https://github.com/asg017/sqlite-vss https://observablehq.com/@asg017/introducing-sqlite-vss

postgres vector pg_vector

vs 
elastic search, opensearch, lucene.
BM25
## Backprop Technqiues 
adam
sgd
with momentum?

## Frameworks

Tensorflow
Pytorch
JAX

Julia

https://github.com/huggingface/accelerate

# Hugging Face
transformers
pipeline is the easy version
datasets library

```python

```

### fastai
## Resources
- Deep Learning Book
- 




# Reinforcement Learning

imitation learning
reinforce
helmut with 3 cameras.

Markov Decision Process
Partially observed mdp (POMDP)

Temporal difference
Reward function
Value function
Q function
policy function
Learn Dynamics - system identification


Q-learning
sarsa
policy gradient
Actor critic



Monte-carlo search

# Verification
[Neural Network Verification with Proof Production](https://arxiv.org/pdf/2206.00512.pdf)

## Resources
[openai spinning up](https://spinningup.openai.com/en/latest/index.html)
Sutton and Barto


[Machine intellgience course](https://www.youtube.com/playlist?list=PLPQUqhKcaBdUYQRyS_g3GFN4L5B-_asUt)

# Old Reinforcement learning

I watched David Silver's lectures on Reinforcement Learning.

http://www0.cs.ucl.ac.uk/staff/d.silver/web/Teaching.html

Pretty interesting stuff.

We had already tried naive reinforcement learning for tic tac toe. We made a random player, and watched whether it won or lost. Then we'd pick only moves that ultimately won and tried to train a neural network to map board state to winning move. In hindsight, this was kind of a ghetto monte carlo policy learning. It worked kind of.

Big takeaways from the lectures:

Value functions and Q functions are things you may want to consider. They tell you the value of your current state. You may want to move to states of high value.

Very evocative of iterative methods for solving matrix equations. So if you're looking for inspiration, look there. If you had the transition probabilities, it is a linear model for the probabilities.

There are table based methods for

There is also a layer of function approximation you can stack on there.

I think you could implement temporal difference learning using common libraries using $latex r_t + \gamma \max_a Q(S,a,\theta)$ as the truth value, and then update the truth values occasionally.







Old:

Reinforcement learning is when you get a rating of a move instead of the right answer. For example a supervised learning task would be to tell whether a picture is of a cat or not.

Also there is a stronger element of time occurring. Reinforcement learning often is sequential in nature. And the rewards may come later down the line rather than immediately

Explore exploit trade off. Exploration allows you to find new things. The new inns are only occasionally better than the stuff you already know about.

The many armed bandit is an example. You have many slot machines to choose from and 100 quarters. Should you try all the slot machines or

greedy method chooses curren best slot

epsilon greedy chooses best while occasionally choosing a random other

Policy is what actions you make given the current state. State is the encapsulation of the important information you've received from all previous measurements. Policy can be deterministic, a function from state to action, or probabilistic, the probability of an action given a state.

Value is the expected reward given a particular policy given your current state.

observations, actions, and rewards.

Three kinds of RL. Policy, Value, and Model based.



There are the questions of policy evaluation and policy optimization. They are related.



Given either a deterministic policy or probabilistic policy, you could hypothetically write down the exact probabilistic step from one time step to another.

There is a connection between Monte Carlo methods I'm more familiar with and the solution methods.

Monte Carlo methods replace expectations with samples. When used numerically, they use expectations as a stand in for a tough summation or integration.

One place where summatiuon occurs is in matrix multiplication. Row times column and then add them all up. Replace this addition with a sampling process.

The evolution of the probability distribution in a markov process can be written as a finite difference equation with a matrix full of the condition steps $latex P(x_{t+1} | x_t)$

The matrix multiplication rule then is one that takes the prior distribution marginalizes it out to give the distribution in the next time step.

The optimization step is also somewhat . It is an interesting analogy that you can produce matrix like systems using (max,+) in the place of the usual (+,*). If you use softmax(a,b) = $latex \ln (e^a + e^b)$ it might even be somewhat invertible (although I have strong suspicions it might easily become numerically unstable).

This is for example used as a way of discussing shortest path problems using edge weight matrices. Mixing between the two is curious.

The world is an oracle that can give us samples for us.

Q(s,a) is a very clever, non obvious function.

To perform a step of the bellman equation without the model of the system, you need a function like that.





Q learning vs SARSA

Q learning is off policy. It pretends you're using a greedy policy

SARSA is on policy



Deep RL course

Imitaiton learning. Learn human expert.

Can often lead to trajectory drifting off course. Clever way of fixing this includes building in some stability to the thing with three headed camera.

Dagger. Make a loop of using human expert. then let thing thing run, then give human the newly acquired data and have him label it. And so on.

Necessary because the poorly imitating robot will end up in states human expert would never see. Distributional mismatch

Model based. If you have am model you can use it. Optimal Control

shooting method, optimize over actions only. Plug in dynamics into cost function

collocation method, optimize over both path and controls with constraints

LQR  - dynamics linear, cost function quadratic. Can be back solved if initial condition problem.

Q_t matrix gives future cost assuming optimal policy in space of u and x

V_t matrix only in space of x

K matrix connects x to u. The feedback matrix. Can be built from blocks of Q.

iterative LQR / Differential dynamic programming (DDP uses second order expansion of dynamics)

go backwards to find the right K. Using it forwards to compute correct x and u. Iterate until convergence

https://homes.cs.washington.edu/~todorov/papers/TassaIROS12.pdf

Model Predictive Control. Do it all like you were playing chess. After each actual time step re-run the iterative LQR

https://people.eecs.berkeley.edu/~svlevine/papers/mfcgps.pdf



https://studywolf.wordpress.com/2016/02/03/the-iterative-linear-quadratic-regulator-method/

https://github.com/pydy/pydy-tutorial-human-standing

https://github.com/openai/roboschool

pybullet



learning the model.

So for example i don't know the mass or inertia parameters (or timestep) of the cartpole in gym. I could build the general model though and then fit pairs of (x, x', u)  to it to determine those. Under random policy.

Usually need to recurse on this step (use current best policy to get more data) like in dagger because random policy discovering dynamics won't go to the same place that better policy does.

Better yet is to use mpc to replan at every step.

Can also directly train a parametrized policy function as part of the loop rather than using the more algorithmic iLQR

Neural network based model of the dynamics might be fine especially since you can backpropagate which is nice for the iterative LQR step.

https://rse-lab.cs.washington.edu/papers/robot-rl-rss-11.pdf

in global models the planning stage will tend to try to exploit regions that are crappily modelled.

maximum entropy. May want to have the most random solution that doesn't hurt cost?

Local models try to avoid this by just modelling gradients? And simply. But use a contrained optimization problem to make sure the robot stays in a region where the local estimates still apply. Trust regions. Defined using how unlikely the current trajectory is


