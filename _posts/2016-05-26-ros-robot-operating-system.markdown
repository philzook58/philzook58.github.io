---
author: philzook58
comments: true
date: 2016-05-26 21:18:25+00:00
layout: post
link: https://www.philipzucker.com/ros-robot-operating-system/
slug: ros-robot-operating-system
title: 'ROS: robot operating system'
wordpress_id: 335
---

I was following mac install instructions

[http://wiki.ros.org/jade/Installation/OSX/Homebrew/Source](http://wiki.ros.org/jade/Installation/OSX/Homebrew/Source)

, but the pip instruction failed. I turned off the anaconda distro I recently installed by commenting out the line in my ~/.profile file

assimp.hpp not found or some stuff

brew info assimp


brew install ros/deps/pyassimp




I give up on mac. It sucks. Using an ubuntu virtual box. Setup is super easy. Mostly just a apt-get


[http://wiki.ros.org/ROS/Tutorials](http://wiki.ros.org/ROS/Tutorials)

So what is ROS? Well, my impression is that it's focus is kind of like unix piping. It's a uniform interface you can use to ram little chunks of programs into one another.

But also the community just has a bunch of robotics programs

rviz

urdf

gazebo

pcl

Check this out [http://wiki.ros.org/visp](http://wiki.ros.org/visp). Depending on how well this works could be pretty cool.

    
    sudo apt-get install ros-jade-visp


You need to be running roscore in another window for stuff to work

Install instructions here

[http://wiki.ros.org/vision_visp?distro=jade](http://wiki.ros.org/vision_visp?distro=jade)

had problems at catkin_make

    
    <code><span class="pln">pip install catkin_pkg</span></code>


nope.

Okay the problem I had was that a weirdo python distro had been install doing something else (Goddamn you Moose. What gives you the right?), so I removed it and had to rerun all the workspace creation stuff. Now we're good






