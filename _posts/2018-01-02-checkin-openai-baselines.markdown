---
author: philzook58
comments: true
date: 2018-01-02 16:18:04+00:00
layout: post
link: https://www.philipzucker.com/checkin-openai-baselines/
slug: checkin-openai-baselines
title: Checkin out the OpenAI Baselines
wordpress_id: 956
---

These are my notes on trying to edit the opeai baselines codebase to balance a cartpole from the down position. They are pretty scattered.

First I just run the built in examples to get a feel and try out deepq networks.

The PPO algorithm at the bottom is the reccommended one still I think. I got the pole kind of upright and would balance for a couple seconds maybe. Work in progress. The ppo example has some funky batching going on that you need to reshape your observations for.





https://github.com/openai/baselines

Some of these are ready to roll on anything you throw at them

They use python3.

pip3 install tensorflow-gpu

pip3 install cloudpickle

running a deepq cartpole example

checkout source

https://github.com/openai/baselines/blob/master/baselines/deepq/experiments/train_cartpole.py

    
        act = deepq.learn(
            env,
            q_func=model,
            lr=1e-3,
            max_timesteps=100000,
            buffer_size=50000,
            exploration_fraction=0.1,
            exploration_final_eps=0.02,
            print_freq=10,
            callback=callback
        )


what is all this shit.

Has quickly suppressed  exploration

has a clear upward trend. But the increase dies off at episode 300 or so. Learning rate decay?

took around 300 episodes to reach reward 200

    
    python3 -m baselines.deepq.experiments.enjoy_cartpole


Pretty good looking

The pong trainer is now called run_atari.py

sudo apt install python3-opencv

Hmm. Defaults to playing breakout actually. Highly exploratory at first. Still basically totally random after a couple mins

The buffer size is actually smaller than I'd expected. 10000?

simple.py is where the learn function is defined.

Hmmm explloration fraction is fraction of time for random play to be turned off over.

Is it getting better? Maybe. Still at 90% random. reward ~0.2

After about 2 hours 13,000 episodes still at 32% exploration. reward ~ 2

How much is from reduction of randomness, vs improvement of q-network? I suppose I could make a graph of reward vs exploration % using current network



trying ppo2 now (this is apparently openai goto method at the moment for first attempt)

https://blog.openai.com/openai-baselines-ppo/

I don't know what to attribute this to necessarily but it is very quickly outperforming the q learning

like in 30seconds

clipfrac is probably how often the clipping bound gets hit

approxkl is approximate kullback-leibler divergence

looking inside the networks,

pi is the move probability distribution layer

vf is the value function

The MlpPolicy class will be useful for lower dimensional tasks. That is the multilayer perceptron, using  a bunch of fully connected layers

on a non simulated system, lower processor count to 1. The -np option on mpirun

Or just follow the mujoco example which is using only 1 cpu

Ah. This whole time it was saving in the /tmp folder in a time stamped folder





without threshold stopping, the thing went absolutely insane. You need to box in the pole



trying to make the square of height, so  that it more emphasizes a total height achieved? Maybe only give reward for new record height? + any height nearly all the way up

beefing up the force magntidue. I think it is a little too wimpy to get it over vertical

Maybe lower episode end so it spends more time trying to get higher than trying to just stay in bounds

Wait, should I not add those vector wrapper guys?



Hey! Sort of kind of success... It gets it up there sometimes, but then it can't really keep it up there... That's odd.

Wow. This is not a good integrator. Under no force the pendulum is obviously gaining energy. Should that matter much? I switched around the ordering to get a leapfrog. Much better.

custom cartpole instance to work from down position and editted to work with ppo2. To more closely match mujoco example, i switched from discrete actions to a continuous choice. I was trying to shape the reward to keep it in bounds. We're getting there maybe. Picking the starting position happens in reset. Most everything else is a straight copy from the gym env

    
    import logging
    import math
    import gym
    from gym import spaces
    from gym.utils import seeding
    import numpy as np
    
    logger = logging.getLogger(__name__)
    
    class CartPoleEnv(gym.Env):
        metadata = {
            'render.modes': ['human', 'rgb_array'],
            'video.frames_per_second' : 50
        }
    
        def __init__(self):
            self.gravity = 9.8
            self.masscart = 1.0
            self.masspole = 0.1
            self.total_mass = (self.masspole + self.masscart)
            self.length = 0.5 # actually half the pole's length
            self.polemass_length = (self.masspole * self.length)
            self.force_mag = 30.0
            self.tau = 0.02  # seconds between state updates
    
            # Angle at which to fail the episode
            # we expect full swings
            self.theta_threshold_radians =  np.pi  #12 * 2 * math.pi / 360
            self.x_threshold = 2.4
    
            # Angle limit set to 2 * theta_threshold_radians so failing observation is still within bounds
            high = np.array([
                self.x_threshold * 2,
                np.finfo(np.float32).max,
                self.theta_threshold_radians * 2,
                np.finfo(np.float32).max])
            high2 = np.array([1])
            self.action_space = spaces.Box(-high2, high2)# spaces.Discrete(2)
            self.observation_space = spaces.Box(-high, high)
    
            self._seed()
            self.viewer = None
            self.state = None
    
            self.steps_beyond_done = None
            self.steps = 0
            self.num_envs = 1
            self.viewer = None
        viewer = None
        def _seed(self, seed=None):
            self.np_random, seed = seeding.np_random(seed)
            return [seed]
    
        def _step(self, action):
            #assert self.action_space.contains(action), "%r (%s) invalid"%(action, type(action))
            #print(action)
            action =action[0] # max(-1, min(action[0],1))
            state = self.state
            x, x_dot, theta, theta_dot = state
            #force = self.force_mag if action==1 else -self.force_mag
            force = self.force_mag * action
            #print(action)
            #print(state)
    
            x  = x + self.tau * x_dot
            theta = theta + self.tau * theta_dot
            costheta = math.cos(theta)
            sintheta = math.sin(theta)
            temp = (force + self.polemass_length * theta_dot * theta_dot * sintheta) / self.total_mass
            thetaacc = (self.gravity * sintheta - costheta* temp) / (self.length * (4.0/3.0 - self.masspole * costheta * costheta / self.total_mass))
            xacc  = temp - self.polemass_length * thetaacc * costheta / self.total_mass
            
            x_dot = x_dot + self.tau * xacc
            
            theta_dot = theta_dot + self.tau * thetaacc
            self.state = (x,x_dot,theta,theta_dot)
            
            done =  x < -self.x_threshold \
                    or x > self.x_threshold \
                    or theta < -np.pi * 2 \
                    or theta > np.pi * 4 \
                    or self.steps > 1024
            done = bool(done)
            
            self.steps += 1
            limit = 200
    
            reward = 0.0
            if  x < -self.x_threshold or x > self.x_threshold:
                reward -= 1.0
            reward += (np.cos(theta)+1)**2
            reward -= 0.1 * action**2 
            reward -= 0.1 * x**2 
            #reward = reward/2048
            '''
            if not done:
                reward = 1.0
            elif self.steps_beyond_done is None:
                # Pole just fell!
                self.steps_beyond_done = 0
                reward = 1.0
            else:
                if self.steps_beyond_done == 0:
                    logger.warning("You are calling 'step()' even though this environment has already returned done = True. You should always call 'reset()' once you receive 'done = True' -- any further steps are undefined behavior.")
                self.steps_beyond_done += 1
                reward = 0.0
            '''
            #print(np.array(self.state).reshape((1,-1)), reward, done, {})
            return np.array(self.state).reshape((1,-1)), reward, done, {}
    
        def _reset(self):
            #self.state = self.np_random.uniform(low=-0.05, high=0.05, size=(4,))
            #x, xdot, theta, thetadot
            self.state = np.array([0, 0, np.pi, 0])
            self.steps_beyond_done = None
            self.steps = 0
            return np.array(self.state).reshape((1,-1))
    
        def _render(self, mode='human', close=False):
            if close:
                if self.viewer is not None:
                    self.viewer.close()
                    self.viewer = None
                return
    
            screen_width = 600
            screen_height = 400
    
            world_width = self.x_threshold*2
            scale = screen_width/world_width
            carty = 100 # TOP OF CART
            polewidth = 10.0
            polelen = scale * 1.0
            cartwidth = 50.0
            cartheight = 30.0
    
            if self.viewer is None:
                from gym.envs.classic_control import rendering
                self.viewer = rendering.Viewer(screen_width, screen_height)
                l,r,t,b = -cartwidth/2, cartwidth/2, cartheight/2, -cartheight/2
                axleoffset =cartheight/4.0
                cart = rendering.FilledPolygon([(l,b), (l,t), (r,t), (r,b)])
                self.carttrans = rendering.Transform()
                cart.add_attr(self.carttrans)
                self.viewer.add_geom(cart)
                l,r,t,b = -polewidth/2,polewidth/2,polelen-polewidth/2,-polewidth/2
                pole = rendering.FilledPolygon([(l,b), (l,t), (r,t), (r,b)])
                pole.set_color(.8,.6,.4)
                self.poletrans = rendering.Transform(translation=(0, axleoffset))
                pole.add_attr(self.poletrans)
                pole.add_attr(self.carttrans)
                self.viewer.add_geom(pole)
                self.axle = rendering.make_circle(polewidth/2)
                self.axle.add_attr(self.poletrans)
                self.axle.add_attr(self.carttrans)
                self.axle.set_color(.5,.5,.8)
                self.viewer.add_geom(self.axle)
                self.track = rendering.Line((0,carty), (screen_width,carty))
                self.track.set_color(0,0,0)
                self.viewer.add_geom(self.track)
    
            if self.state is None: return None
    
            x = self.state
            cartx = x[0]*scale+screen_width/2.0 # MIDDLE OF CART
            self.carttrans.set_translation(cartx, carty)
            self.poletrans.set_rotation(-x[2])
    
            return self.viewer.render(return_rgb_array = mode=='rgb_array')




    
    #!/usr/bin/env python
    import argparse
    from baselines import bench, logger
    from custom_cart import CartPoleEnv
    
    def train(env_id, num_timesteps, seed):
        from baselines.common import set_global_seeds
        from baselines.common.vec_env.vec_normalize import VecNormalize
        from baselines.ppo2 import ppo2
        from baselines.ppo2.policies import MlpPolicy
        import gym
        import tensorflow as tf
        from baselines.common.vec_env.dummy_vec_env import DummyVecEnv
        ncpu = 1
        config = tf.ConfigProto(allow_soft_placement=True,
                                intra_op_parallelism_threads=ncpu,
                                inter_op_parallelism_threads=ncpu)
        tf.Session(config=config).__enter__()
        def make_env():
            env = CartPoleEnv()#gym.make(env_id)
            env = bench.Monitor(env, logger.get_dir())
            return env
        env = DummyVecEnv([make_env])
        env = VecNormalize(env)
        #env = CartPoleEnv()
        set_global_seeds(seed)
        policy = MlpPolicy
        ppo2.learn(policy=policy, env=env, nsteps=2048, nminibatches=32,
            lam=0.95, gamma=0.99, noptepochs=10, log_interval=1,
            ent_coef=0.0,
            lr=3e-4,
            cliprange=0.2,
            total_timesteps=num_timesteps,
            save_interval=1)
    
    
    def main():
        parser = argparse.ArgumentParser(formatter_class=argparse.ArgumentDefaultsHelpFormatter)
        parser.add_argument('--env', help='environment ID', default='Hopper-v1')
        parser.add_argument('--seed', help='RNG seed', type=int, default=0)
        parser.add_argument('--num-timesteps', type=int, default=int(1e6))
        args = parser.parse_args()
        logger.configure()
        train(args.env, num_timesteps=args.num_timesteps, seed=args.seed)
    
    
    if __name__ == '__main__':
        main()


A script to view resulting network

    
    from baselines.ppo2 import ppo2
    import pickle
    import tensorflow as tf
    import numpy as np
    ncpu = 1
    
    filebase = '/tmp/openai-2017-12-27-18-56-28-890229/'
    modelfile = filebase + 'checkpoints/00466'
    
    
    config = tf.ConfigProto(allow_soft_placement=True,
                            intra_op_parallelism_threads=ncpu,
                            inter_op_parallelism_threads=ncpu)
    tf.Session(config=config).__enter__()
    output = open(filebase + 'make_model.pkl', 'rb')
    model =  pickle.load(output)()
    
    
    model.load(modelfile)
    
    dones = [False]
    states = [None]
    obs = np.array([[0,0,np.pi,0]])
    
    actions, values, states, neglogpacs = model.step(obs, states, dones)
    
    from custom_cart import CartPoleEnv
    
    env = CartPoleEnv()
    ob = env.reset()
    done = False
    for i in range(2000):
    
    	actions, values, states, neglogpacs = model.step(ob.reshape((1,-1)), states, dones)
    	action = actions[0]
    	ob, reward, done, _ = env.step(action)
    	env.render()











