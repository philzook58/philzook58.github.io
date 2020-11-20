---
author: philzook58
comments: true
date: 2016-11-20 05:49:42+00:00
layout: post
link: https://www.philipzucker.com/python-xbox-controller-mac/
slug: python-xbox-controller-mac
title: Python Xbox Controller Mac
wordpress_id: 556
---

Working on a raspberry pi based robot car right now and wanted to get an xbox controller to control it.

Tried using the python package inputs. Didn't work

Had to uninstall and reinstall latest version of mac xbox driver

https://github.com/360Controller/360Controller

PyGame ended up working. Then Pickling to serialize and pumping over udp. Here's the sending and receiving program.

    
    import pygame
    import sys
    import time
    import socket
    import cPickle as pickle
    
    UDP_IP = "127.0.0.1"
    UDP_PORT = 5005
    MESSAGE = "Hello, World!"
    
    print "UDP target IP:", UDP_IP
    print "UDP target port:", UDP_PORT
    print "message:", MESSAGE
    
    sock = socket.socket(socket.AF_INET, # Internet
                         socket.SOCK_DGRAM) # UDP
    
    
    pygame.init()
    
    pygame.joystick.init()
    clock = pygame.time.Clock()
    
    print pygame.joystick.get_count()
    _joystick = pygame.joystick.Joystick(0)
    _joystick.init()
    while 1:
    	for event in pygame.event.get():
    		if event.type == pygame.JOYBUTTONDOWN:
    			print("Joystick button pressed.")
    			print event
    		if event.type == pygame.JOYAXISMOTION:
    			#print _joystick.get_axis(0)
    			#print event
    			if event.axis == 0: # this is the x axis
    				print event.value
    			if event.axis == 5: # right trigger
    				print event.value
    	xdir = _joystick.get_axis(0)
    
    	rtrigger = _joystick.get_axis(5)
    	#deadzone
    	if abs(xdir) < 0.2:
    		xdir = 0.0
    	if rtrigger < -0.9:
    		rtrigger = -1.0
    
    	MESSAGE = pickle.dumps([xdir,rtrigger])
    	sock.sendto(MESSAGE, (UDP_IP, UDP_PORT))
    
    	clock.tick(30)
    
    
    		
    
    	'''
    	print _joystick.get_init()
    	print _joystick.get_id()
    	print _joystick.get_name()
    	print _joystick.get_numaxes()
    	print _joystick.get_numballs()
    	print _joystick.get_numbuttons()
    	print _joystick.get_numhats()
    	print _joystick.get_axis(0)
    	print _joystick.get_button(0)
    	n = _joystick.get_numbuttons()
    	axesnum = _joystick.get_numaxes()
    	for i in range(axesnum):
    		print _joystick.get_axis(i)
    		'''
    
    #while(1):
    #	for i in range(n):
    



    
    import socket
    import cPickle as pickle
    
    UDP_IP = "127.0.0.1"
    UDP_PORT = 5005
    
    sock = socket.socket(socket.AF_INET, # Internet
                         socket.SOCK_DGRAM) # UDP
    sock.bind((UDP_IP, UDP_PORT))
    
    while True:
        data, addr = sock.recvfrom(1024) # buffer size is 1024 bytes
        print "received message:", pickle.loads(data)











