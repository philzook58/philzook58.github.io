---
author: philzook58
comments: true
date: 2016-10-31 03:20:25+00:00
layout: post
link: https://www.philipzucker.com/shaders-raymarching/
slug: shaders-raymarching
title: Shaders, Raymarching
wordpress_id: 535
tags:
- glsl
- raymarching
- shaders
- shadertoy
---

Here is the minimal picture i have of how a graphics card works.

There are two main stages, the vertex shader and the fragment shader. The vertex shader is given a list of triangles basically. It computes and applies the transformations necessary to rotate and translate the camera position for the vertices and compute normal vectors and some other geometrical things.

The fragments shader is then passed info from the vertex shader. It has to output a color by setting a variable fragColor. There are variables called that are given the type annotation varyings that are automatically interpolated in the vertex (think of smoothly rotating vectors or colors between vertices). The fragment shader is called once per pixel on the screen.

Mostly information is passed around via pointer rather than function return (I guess that is kind of a common C paradigm and it does make sense.). What does suck about that is you'll see variables appear out of nowhere. They are basically global variables from your codes perspective. I assume there is a limited number of them so you get used to it.

shadertoy.com is awesome. It draws a big rectangle and gives you easy access to the fragment shader with some useful extra variables available to you.

It feels like a big map in the functional sense. You write a shader function and then the gpu runs

    
    pixelcolor = map shader pixelinfo


This is refreshing. The api I'm used to is an imperative api where you consecutively mutate some screen object by called line or point or circle on it. Not that that's bad, necessarily. But I do like the newness.

This will draw a white circle.

    
    void mainImage( out vec4 fragColor, in vec2 fragCoord )
    {
        vec2 coord = fragCoord.xy - iResolution.xy/2.0; 
        if(length(coord) < 100.0){
        	fragColor = vec4(1);
        }
        else{
        
        fragColor = vec4(0);
        }
        
    }




Also here is a raymarched sphere with a little lighting. Ray marching uses the distance function to push the ray smart distances. There are a ton of things you could do here. Could optimize the loop to break when rays get close enough, or when they fly off to infinity.



http://jamie-wong.com/2016/07/15/ray-marching-signed-distance-functions/





    
    float sphere( in vec3 p){
     return length(p) - 0.5;
        
    }
    
    void mainImage( out vec4 fragColor, in vec2 fragCoord )
    {
    	vec2 uv = fragCoord.xy / iResolution.y;
        vec2 st = 2.0*uv -1.0;
    	fragColor = vec4(uv,0.5+0.5*sin(iGlobalTime),1.0);
        vec3 cam = vec3(0.0, 0.0, -1.0);
        vec3 ray = vec3(st.x, st.y, 1);
        ray = normalize(ray);
        float depth = 0.0;
        for(int i=0; i<64; i++){
         vec3 p = cam + depth * ray;
         depth = depth += sphere(p);
            
        }
        vec3 p = cam + depth * ray;
        if(abs(sphere(p)) < 0.1){
         
         fragColor = vec4(0.3+dot(normalize(p), normalize(vec3(1.0,1.0,0.0)))); 
        }
        
    }







