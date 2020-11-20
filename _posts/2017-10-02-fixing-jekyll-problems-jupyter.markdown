---
author: philzook58
comments: true
date: 2017-10-02 19:23:11+00:00
layout: post
link: https://www.philipzucker.com/fixing-jekyll-problems-jupyter/
slug: fixing-jekyll-problems-jupyter
title: Fixing up some jekyll problems for jupyter
wordpress_id: 898
---

the jupyer jekyll plugin supposedly won't work on github pages

https://briancaffey.github.io/2016/03/14/ipynb-with-jekyll.html

jupyter nbconvert --to markdown jekyll_test.ipynb

To get latex (including the $ tags) to work on the minima layout I added

    
    <head>
      <meta charset="utf-8">
      <meta http-equiv="X-UA-Compatible" content="IE=edge">
      <meta name="viewport" content="width=device-width, initial-scale=1">
      <link rel="stylesheet" href="{{ "/assets/main.css" | relative_url }}">
      <link rel="alternate" type="application/rss+xml" title="{{ site.title | escape }}" href="{{ "/feed.xml" | relative_url }}">
      {% if jekyll.environment == 'production' and site.google_analytics %}
        {% include google-analytics.html %}
      {% endif %}
      <script type="text/x-mathjax-config">
    MathJax.Hub.Config({
      tex2jax: {inlineMath: [['$','$'], ['\\(','\\)']]}
    });
    </script>
    <script type="text/javascript" async
      src="https://cdnjs.cloudflare.com/ajax/libs/mathjax/2.7.2/MathJax.js?config=TeX-MML-AM_CHTML">
    </script>
    </head>


into an _includes/head.html





I added a pynb  directory and added the following into my _config file? Not sure this was necessary.

    
    defaults:
    - scope:
        path: "pynb"
      values:
        image: true




replace all

fermions_part_1_files

with

/pynb/fermions_part_1_files

in the markdown file.

could also add syntax highlighting but maybe this is good enough.
