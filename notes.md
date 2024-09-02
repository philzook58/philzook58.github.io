---
layout: page
title: Notes
permalink: /notes/
my_array:
  - Docket
  - CS
  - Languages
  - Logic
  - Math
  - Misc
  - Physics
  - Programming
  - Engineering
  - CyberSecurity
---
More fluid than posts. Unfinished thoughts. Link Dumps. I will hopefully continually rearrange and crosslink these. It can look way more cogent in the [markdown sources](https://github.com/philzook58/philzook58.github.io/tree/master/_notes). I don't really look at the rendered version often.

Actually, I got kind of overwhelmed organizing these once they grew to a certain point, so I declared bankruptcy and returned to more local drafts.

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
