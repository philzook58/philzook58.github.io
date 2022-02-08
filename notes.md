---
layout: page
title: Notes
permalink: /notes/
my_array:
  - CS
  - Languages
  - Logic
  - Math
  - Misc
  - Physics
  - Programming
---
More fluid than posts. Unfinished thoughts. Link Dumps. I will hopefully continually rearrange and crosslink these.

{% for folder in page.my_array  %}
<h2> {{ folder }} </h2>
<ul>
  {% for item in site.notes  %}
    {% assign pathpieces = item.url | split: "/" %}
    {% if pathpieces[-2] == folder %}
    <li><a href="{{ item.url }}">{{ item.title }} </a></li>
    {% endif %}
  {% endfor %}
  </ul>
{% endfor %}
