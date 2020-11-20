---
author: philzook58
comments: true
date: 2017-12-01 03:56:10+00:00
layout: post
link: https://www.philipzucker.com/downloading-collecting-coursera-videos/
slug: downloading-collecting-coursera-videos
title: Downloading and Collecting Coursera videos
wordpress_id: 931
---

I like to watch and listen to my coursera videos on my commute. The app has download functionality but the quizzes and crap require your intervention. I need just a block of stuff so I can be hands free.

coursera-dl is a command line tool to download coursera content

https://github.com/coursera-dl/coursera-dl

basic usage is like so

coursera-dl -h is a help menu

you can pass in your username and password with -u and -p or setup a ~/.netrc file as described in the README

coursera-dl --list-courses -n

I think it should list courses by default honestly.

This downloads all mp4 videos

coursera-dl cloud-computing -n -f "mp4"



I then made a dirty script that will go through each week and concatenate the videos of that week hopefully in order into a single mp4 file. It is not a clean script. It will throw some errors and build some weird extra files, but it gets the job done. Run it in the course directory

    
    #!/bin/bash
    
    #maybe if you want to pre speedup. It's slow though
    #ffmpeg -i input-video.mp4 -vf "setpts=0.68*PTS" -filter:a "atempo=1.467" output-video.mp4
    
    #makes a directory and builds one video per week
    
    #mkdir videos
    
    for D in `find . -type d` -maxdepth 1
    do
     #if [["$D" != "videos/"]]; then
     #//Do whatever you need with D
     find $D -name \*.mp4 -print | sort > videolist.txt
     sed -i -e 's/^/file /' videolist.txt 
     ffmpeg -f concat -safe 0 -i videolist.txt -codec copy ./$D.mp4
    #fi
    done









