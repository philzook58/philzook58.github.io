---
author: philzook58
comments: true
date: 2016-02-29 19:13:02+00:00
layout: post
link: https://www.philipzucker.com/vomitting-out-some-machine-learning-with-torch/
slug: vomitting-out-some-machine-learning-with-torch
title: Vomitting Out Some Machine Learning with Torch
wordpress_id: 404
tags:
- lua
- machine learning
- torch
---

Don't know anything about Lua or Torch, and not so much about machine learning. Little project to get going.

Torch is to Lua what Numpy is to python. Never done any lua before, although for a while it was the main language on the esp8266. Torch seems like a popular base for machine learning in competition with theano and tensorflow. Lua is like if python and javascript has a slightly retarded baby.

Thought I'd give a simple tic tac toe playing guy a go. The structure is play a bunch of totally random games, collect up all the winning games. Then the problem is a classification problem where the categories are the next move (1-9).

Then used the stock nn neural network package to learn on it. Had a tough time finding clear docs. I am unimpressed.

Then use trained neural network to play against the random component.

The win stats increased from ~28% to ~45% (with some fluctuations run to run of a couple percent). Not bad. Especially since going second is disadvantageous. Okay, as I wrote that I realized it's easy to try flipping that. Going first the stats go from 59% to 69%.

Hmmm. Maybe I should look at draws?

Also, a smart strategy for the moves would be to use the suggested moves according to their rank, not using the top suggested move then if that is invalid using a random move.

{% highlight lua %}
{% raw %}
    math.randomseed(os.time())
    
    function won(board,x)
      --diagonals
      if board[1][1] == x and board[2][2]==x and board[3][3] == x then
        return true
      end
    
      if board[1][3] == x and board[2][2]==x and board[3][1] == x then
        return true
      end
    
    --rows
      for i=1,3 do
        if board[i][3] == x and board[i][2]==x and board[i][1] == x then
          return true
        end
      end
    --columns
      for i=1,3 do
        if board[1][i] == x and board[2][i]==x and board[3][i] == x then
          return true
        end
      end
    
      return false
    
    end
    
    
    function full(board)
      for i=1,3 do
        for j=1,3 do
          if board[i][j] == '' then
            return false
          end
        end
      end
    
      return true
    end
    
    
    function mapBoardtoNum(board)
      newboard = {{},{},{}}
      for i=1,3 do
        for j=1,3 do
          if board[i][j] == 'x' then
            newboard[i][j] = 1
          end
          if board[i][j] == '' then
            newboard[i][j] = 0
          end
          if board[i][j] == 'o' then
            newboard[i][j] = -1
          end
        end
      end
      return newboard
    end
    
    --[[
    print(won({
    {'x','',''},
    {'x','o',''},
    {'x','o',''}}, 'o'))
    ]]
    
    
    mymoves = {}
    myboards = {}
    wins = 0
    gamenum = 10000
    for k=1,gamenum do
    
      board = {{'','',''},
      {'','',''},
      {'','',''}}
    
      move = 'o'
    
      game = {}
      choices = {}
    
      turn = 1
    
      while not won(board,'x') and not won(board,'o') and not full(board) do
    
        if move == 'x' then
          move = 'o'
        elseif move == 'o' then
          move = 'x'
        end
    
        repeat
          i = math.random(3)
          j = math.random(3)
        until board[i][j] == ''
    
        if move == 'x' then
          game[turn] = mapBoardtoNum(board)
          choices[turn] = i -1 + 3 * (j-1) +1
          turn = turn + 1
      end
        board[i][j] = move
    
      end
    
      if won(board,'x') then
        wins = wins +1
        for i = 1,#game do
          table.insert(myboards, game[i])
          table.insert(mymoves, choices[i])
        end
      end
    
    end
    
    --print(mymoves)
    --print(#myboards)
    print('won ' .. wins ..' out of ' .. gamenum)
    
    training = {}
    --[[
    training.data = torch.Tensor(myboards)
    training.labels = torch.Tensor(mymoves)
    training.size = function() return (#mymoves) end
    ]]
    
    training.size = function() return (#mymoves) end
    for i=1,training:size() do
      training[i] = {torch.Tensor(myboards[i]), torch.Tensor({mymoves[i]})}
    end
    
    ninputs = 9
    nhiddens = 30
    noutputs = 9
    require 'nn'
    model = nn.Sequential()
    model:add(nn.Reshape(ninputs))
    model:add(nn.Linear(ninputs,nhiddens))
    model:add(nn.Tanh())
    model:add(nn.Linear(nhiddens,noutputs))
    model:add( nn.LogSoftMax() )
    
    criterion = nn.ClassNLLCriterion()
    
    
    trainer = nn.StochasticGradient(model, criterion)
    trainer.learningRate = 0.01
    trainer.maxIteration = 7
    
    trainer:train(training)
    
    
    
    
    --[[
    print(board)
    print(won(board,'o'))
    print(won(board,'x'))
    print(choices)
    print(game[1])
    ]]
    
    
    board = {
    {'x','o',''},
    {'x','o',''},
    {'x','o',''}
    }
    
    logprobs= model:forward(torch.Tensor(mapBoardtoNum(board)))
    print(logprobs)
    max, pred =torch.max(logprobs,1)
    print(max)
    print(pred)
    --[[
    -- Basic format
    {
    {'x','o',''},
    {'x','o',''},
    {'x','o',''}
    }
    ]]
    
    print('random won ' .. wins ..' out of ' .. gamenum)
    
    
    mymoves = {}
    myboards = {}
    wins = 0
    for k=1,gamenum do
    
      board = {{'','',''},
      {'','',''},
      {'','',''}}
    
      move = 'o'
    
      game = {}
      choices = {}
    
      turn = 1
    
      while not won(board,'x') and not won(board,'o') and not full(board) do
        --print('yo')
        if move == 'x' then
          move = 'o'
          repeat
            i = math.random(3)
            j = math.random(3)
          until board[i][j] == ''
          board[i][j] = move
    
    
        elseif move == 'o' then
          move = 'x'
          --print(board)
          --print(torch.Tensor(mapBoardtoNum(board)))
          local probs = model:forward(torch.Tensor(mapBoardtoNum(board)))
          maxs, pred = torch.max(probs,1)
          --i -1 + 3 * (j-1) +1
          pred = pred - 1
          i = pred % 3 + 1
          j = (pred - pred%3) / 3 + 1
          i = i[1]
          j = j[1]
          --print(i[1])
          --print(j)
          --print(board)
          --print(board[i][j])
          if board[i][j] == '' then
            board[i][j] = move
          else
              repeat
                i = math.random(3)
                j = math.random(3)
              until board[i][j] == ''
              board[i][j] = move
          end
    
    
    
        end
    
      end
    
      if won(board,'x') then
        wins = wins +1
      end
    
    end
    
    print('learned won ' .. wins ..' out of ' .. gamenum)
    
{% endraw %}
{% endhighlight %}


