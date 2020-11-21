---
author: philzook58
comments: true
date: 2017-12-19 20:08:07+00:00
layout: post
link: https://www.philipzucker.com/?p=940
published: false
slug: Real World Cartpole
title: Real World Cartpole
wordpress_id: 940
---

We got some sweet aluminum extrusion to use as a rail

We had some parts that pasically served the needs from a delta printer project. Including a fully 3d printed linear carriage which is pretty dang useful and simple

To start we decided to go wtih Q-learning.

We made a version that had a potentiometer and implemented PID control. It worked ok ish for balancing the stick. It took a lot of fiddling.

One confusing thing is that the motor control mostly corresponds to velocity control. A constant velocity of the cart applies to torques to the pole, acceleration applies torques. So really the I and P terms are the most relevant ones, and they sort of don't work in the manner that you'd naively think. Normally, P terms get you most of the way there and you add in a little I to remove any constant offset of the control position. But in our case the I terms acts more like a P term and the P term more like a D term, damping oscillations.

We are using an opencv color detector with colored tags and a ps eye camera. Ps Eyes are cheap and they get pretty high framerates. Unfortunately OpenCV has a 5 frame latency which degrades performance.

Using Keras with tensorflow to implement the neural network.

We had a motor control controllable over USB serial.



Some thoughts

    
    import keras
    from keras.models import Sequential
    from keras.layers import Dense, Activation
    import keras.backend as K
    
    #I am making a bad sketch of what we need
    #Is sketching a really bad technique?
    
    
    def train
    
    
    action_dim = 4
    state_dim = 3
    
    policymodel = Sequential([
        Dense(32, input_shape=(state_dim,)),
        Activation('relu'),
        Dense(action_dim),
        Activation('softmax'),
    ])
    
    def policy_loss(y_true, y_pred):
    	return K.log(y_pred) * y_true  
    policymodel.compile(optimizer='rmsprop', loss=policy_loss, )
    
    
    
    
    valuemodel = Sequential([
        Dense(32, input_shape=(state_dim,)),
        Activation('relu'),
        Dense(10),
        Activation('relu'),
        Dense(1)
    ])
    
    valuemodel.compile(optimizer='rmsprop', loss='mse' )
    
    
    #SARSA is a lower hanging fruit
    
    
    def policyTrain():
    	vsprime = valuemodel.predict(self, next_states, batch_size=32, verbose=0)
    	rs = lookahead_reward(state)
    	vs = valuemodel.predict(self, states, batch_size=32, verbose=0)
    	vsprime = vs[lookahead:] 
    	policymodel.fit(states , rs + gamma * vsprime - vs, epochs = 1)
    
        # max ln p(s,a) (r + gamma * V(s') - V(s))
    
    def valueTrain(lookahead, states):
    
    	vs = valuemodel.predict(self, states, batch_size=32, verbose=0)
    	rs = rewards(states, lookahead)
    	vsprime = vs[lookahead+1:]
    	valuemodel.fit(states , rs + gamma * vsprime, epochs = 1)
    
    	# train V(s) = r + gamma * V(s')
    
    
    def lookahead_reward(n):
    	reward = rewards(states)
    	for i in range(n):
    		reward[:-i] += gamma * reward[i:] 
    	return reward[:-n]









