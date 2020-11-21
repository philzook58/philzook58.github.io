---
author: philzook58
comments: true
date: 2018-01-30 15:15:44+00:00
layout: post
link: https://www.philipzucker.com/?p=969
published: false
slug: The Duality between Filters and Controllers
title: The Duality between Filters and Controllers
wordpress_id: 969
---

Filters combine noisy measurements with prior information about the dynamics to create good estimates for the hidden state of a system.

Controllers choose actions in order to maximize some objective function of the system.

These two notions are related.

Brian Beckman has been talking about how the type signatures of one time step are the dual of each other.

s->(s,a) is a controller with internal controller state s.

(s,o)->s is a filter with internal filter state s (the running averages and current uncertainties for example).



an environment that produces obsersvations has signature

s' -> (s',o)

and an environment that accepts actions

(s',a)->s'



This is a paper relating the control problem and the filtering problem and shows the explicit mapping between the solution of the Klaman filter and the LQR controller.

https://homes.cs.washington.edu/~todorov/papers/TodorovCDC08.pdf







The observations are the interface between a filter and it's environment. Given fixed observations, we can try to find a sequence of states that best matches them.

The basic model says how the observation is connected to the state on average and also how noisy is it.,

The dynamics are also assumed to have a degree of noisiness.



The noisiness of the dynamics is the relative freedom the environment has to choose perturbations to the mean dynamics.

The noisiness of the measurements is a measure of weather the environment needs to actually push the state to achieve that measurement or not.

The filtering problem of the observations is dual to the environmental problem of trying to find the controls to best produce the observations.

LQR and Kalman

Hypotheses:

Viterbi Algorithm and Table Based Q learning (Value Iteration)?

Particle Filter and Monte Carlo Tree Search?

Model Predictive Control and Moving Window Estimator



type FilterState = [(weights, states)]

type MeasurementUpdate = (o , FilterState) -> FilterState

measupdate proby o filterstate = map (\(w,s)-> (w* (proby o s), s)) filterstate

resample filterstate =






