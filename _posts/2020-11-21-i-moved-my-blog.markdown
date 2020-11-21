---
author: philzook58
comments: true
date: 2020-11-21 01:05:56+00:00
layout: post
link: https://www.philipzucker.com/dataframes-jl-style-linear-relations/
slug: i-moved-my-blog-from-wordpress
title: I Moved My Blog From Wordpress


---

Wordpress has been a source of stress and disatisfaction for a number of years now. As i've been writing my blog posts and becoming more invested in it, it has been concerning to watch my Wordpress site rot. The block editor is clunky and nonresponsive and it seems like the thing is constantly being attacked by bots and spammers. For a while there, I couldn't get code to enter with > signs in it without them being autoreplaced by an escaped version that did not render correctly.

There is also the issue that my blog has become a really useful record that I'd like to continue to exist, perhaps even beyond the lifetime of Wordpress. Better now than never.

I also didn't like how slow rendering it was. I kind of like the pared down raw aesthetic of html like in [danluu.com](danluu.com) or Oleg Kiselyov's site.

In the end, I didn't go totally raw html. I actually started a Jekyll based blog around 2017 where I was going to keep better written posts, but I abandoned it. Here it is live again!

I think by setting my jekyll urls to the titles, links to posts from the Wordpress site should still work.

The old site is still available at [philzucker.nfshost.com](philzucker.nfshost.com) and [philzucker2.nfshost.com](philzucker2.nfshost.com).

For the transfer I used exitwp which is old (python 2), but still worked ok. [https://github.com/some-programs/exitwp](https://github.com/some-programs/exitwp)

I wrote a janky python script to download the images and fix some of the obvious flaws, like it kept the word "latex" in my latex and download gists from the brief period I was embedding Gists because Wordpress's code rendering was so flawed. I still had to go through and manually fix some stuff, but at least it was mostly painless and only took a couple hours.


```python


import re
import textwrap




import os
import urllib
directory = "."

# [gist https://gist.github.com/philzook58/328a29e64cf740c62cbe2138913b59a2#file-properties-py]
import urllib.request

# grep -nr 'yourString*' .
for filename in os.listdir(directory):
    print(filename)
    with open(filename, "r") as f:
        ex = f.read()
    while ex.find("<code>") != -1:
        begin = ex.find("<code>")
        end = ex.find("</code>")
        ex= ex[:begin] +  "\n```\n" + textwrap.dedent(ex[begin-6 : end ]).replace("<code>","") + "\n```\n"   + ex[end+7:]
    ex = ex.replace("$latex", "$")
    #print(re.findall(r'(http\:|https\:)\/\/.*\.(png|jpg|gif)', ex))
    for matchstring in [ r'(http\:\/\/.*?\.(png|jpg|gif))',  r'(https\:\/\/.*?\.(png|jpg|gif))'  ]:
        for image_url, _ in re.findall(matchstring, ex):
        #for image_url in re.findall(r'(?:http\:|https\:)?\/\/(?!.*(fimblylgf|\])).*\.(png|jpg|gif)', ex):
            print("image url", image_url)
            imgfilename = image_url.split("/")
            if len(imgfilename) > 1:
                imgfilename = imgfilename[-1]
                urltail = image_url.split(".com")[-1]
                try:
                    urllib.request.urlretrieve(image_url,  "../assets/" + imgfilename)
                    ex = ex.replace(image_url, "/assets/" + imgfilename)
                except:
                    try:
                        image_url2 = "http://philzucker.nfshost.com" + urltail
                        print("requesting", image_url2)
                        urllib.request.urlretrieve(image_url2,  "../assets/" + imgfilename)
                        ex = ex.replace(image_url, "/assets/" + imgfilename)
                    except:
                        try:
                            image_url2 = "http://philzucker2.nfshost.com" + urltail
                            urllib.request.urlretrieve(image_url2,  "../assets/" + imgfilename)
                            ex = ex.replace(image_url, "/assets/" + imgfilename)
                        except:
                            print("FAILED TO DOWNLOAD", image_url)
                        #print("failure", image_url)
            else:
                print("warning: ", image_url)
    while ex.find("[gist") != -1:
        begin = ex.find("[gist")
        print(begin)
        print(ex[begin: begin+90]) 
        end = (ex[begin:]).find("]") + begin
        urlstart = ex[begin:].find("http") + begin
        print(end)
        print(urlstart)
        gist = ex[ urlstart : end]
        # https://gist.githubusercontent.com/philzook58/328a29e64cf740c62cbe2138913b59a2/raw/properties.py
        print(gist)
        tail = gist.split("/")[-1]
        #print(tail)
        if len(tail.split("#")) > 1:
            (idhash, gistfilename)= tail.split("#")
            gistfilename = ".".join(gistfilename.split("-")[1:])
            rawgist = f"https://gist.githubusercontent.com/philzook58/{idhash}/raw/{gistfilename}"
        else:
            rawgist = f"https://gist.githubusercontent.com/philzook58/{tail}/raw/"
        print(rawgist)
        with urllib.request.urlopen(rawgist) as response:
            code = response.read().decode()
            print(code)
        ex = ex[:begin] + "\n```\n" + code + "\n```\n" + ex[end + 1:]
    with open(filename,"w") as f:
        ex = f.write(ex)
```



An annoying thing is that the drafts are equally important to me. This is often where I kept notes or partial projects and I liked having them organized by date. There might be twice as much in my drafts as there is in actual posts, despite the low bar I've tried to have for posting.

This is a lightly modified version of exitwp that downloads just drafts

```
#!/usr/bin/env python

import codecs
import os
import re
import sys
from datetime import datetime, timedelta, tzinfo
from glob import glob
from urllib import urlretrieve
from urlparse import urljoin, urlparse
from xml.etree.ElementTree import ElementTree, XMLTreeBuilder

import yaml
from bs4 import BeautifulSoup

from html2text import html2text_file

'''
exitwp - Wordpress xml exports to Jekykll blog format conversion

Tested with Wordpress 3.3.1 and jekyll 0.11.2

'''
######################################################
# Configration
######################################################
config = yaml.load(file('config.yaml', 'r'))
wp_exports = config['wp_exports']
build_dir = config['build_dir']
download_images = config['download_images']
target_format = config['target_format']
taxonomy_filter = set(config['taxonomies']['filter'])
taxonomy_entry_filter = config['taxonomies']['entry_filter']
taxonomy_name_mapping = config['taxonomies']['name_mapping']
item_type_filter = set(config['item_type_filter'])
item_field_filter = config['item_field_filter']
date_fmt = config['date_format']
body_replace = config['body_replace']


# Time definitions
ZERO = timedelta(0)
HOUR = timedelta(hours=1)


# UTC support
class UTC(tzinfo):
    """UTC."""

    def utcoffset(self, dt):
        return ZERO

    def tzname(self, dt):
        return 'UTC'

    def dst(self, dt):
        return ZERO


class ns_tracker_tree_builder(XMLTreeBuilder):

    def __init__(self):
        XMLTreeBuilder.__init__(self)
        self._parser.StartNamespaceDeclHandler = self._start_ns
        self.namespaces = {}

    def _start_ns(self, prefix, ns):
        self.namespaces[prefix] = '{' + ns + '}'


def html2fmt(html, target_format):
    #   html = html.replace("\n\n", '<br/><br/>')
    #   html = html.replace('<pre lang="xml">', '<pre lang="xml"><![CDATA[')
    #   html = html.replace('</pre>', ']]></pre>')
    if target_format == 'html':
        return html
    else:
        return html2text_file(html, None)


def parse_wp_xml(file):
    parser = ns_tracker_tree_builder()
    tree = ElementTree()
    print 'reading: ' + wpe
    root = tree.parse(file, parser)
    ns = parser.namespaces
    ns[''] = ''

    c = root.find('channel')

    def parse_header():
        return {
            'title': unicode(c.find('title').text),
            'link': unicode(c.find('link').text),
            'description': unicode(c.find('description').text)
        }

    def parse_items():
        export_items = []
        xml_items = c.findall('item')
        for i in xml_items:
            taxanomies = i.findall('category')
            export_taxanomies = {}
            for tax in taxanomies:
                if 'domain' not in tax.attrib:
                    continue
                t_domain = unicode(tax.attrib['domain'])
                t_entry = unicode(tax.text)
                if (not (t_domain in taxonomy_filter) and
                    not (t_domain
                         in taxonomy_entry_filter and
                         taxonomy_entry_filter[t_domain] == t_entry)):
                    if t_domain not in export_taxanomies:
                        export_taxanomies[t_domain] = []
                    export_taxanomies[t_domain].append(t_entry)

            def gi(q, unicode_wrap=True, empty=False):
                namespace = ''
                tag = ''
                if q.find(':') > 0:
                    namespace, tag = q.split(':', 1)
                else:
                    tag = q
                try:
                    result = (i.find(q, ns) or i.find(tag) or i.find(ns[namespace] + tag)).text.strip()
                    print result.encode('utf-8')
                except AttributeError:
                    result = 'No Content Found'
                    if empty:
                        result = ''
                if unicode_wrap:
                    result = unicode(result)
                return result

            body = gi('content:encoded')
            for key in body_replace:
                # body = body.replace(key, body_replace[key])
                body = re.sub(key, body_replace[key], body)

            img_srcs = []
            if body is not None:
                try:
                    soup = BeautifulSoup(body)
                    img_tags = soup.find_all('img')
                    for img in img_tags:
                        img_srcs.append(img['src'])
                except:
                    print 'could not parse html: ' + body
            # print img_srcs

            excerpt = gi('excerpt:encoded', empty=True)

            export_item = {
                'title': gi('title'),
                'link': gi('link'),
                'author': gi('dc:creator'),
                'date': gi('wp:post_date'),
                'slug': gi('title'), #gi('wp:post_name'),
                'status': gi('wp:status'),
                'type': gi('wp:post_type'),
                'wp_id': gi('wp:post_id'),
                'parent': gi('wp:post_parent'),
                'comments': gi('wp:comment_status') == u'open',
                'taxanomies': export_taxanomies,
                'body': body,
                'excerpt': excerpt,
                'img_srcs': img_srcs
            }

            export_items.append(export_item)

        return export_items

    return {
        'header': parse_header(),
        'items': parse_items(),
    }


def write_jekyll(data, target_format):

    sys.stdout.write('writing')
    item_uids = {}
    attachments = {}

    def get_blog_path(data, path_infix='jekyll'):
        name = data['header']['link']
        name = re.sub('^https?', '', name)
        name = re.sub('[^A-Za-z0-9_.-]', '', name)
        return os.path.normpath(build_dir + '/' + path_infix + '/' + name)

    blog_dir = get_blog_path(data)

    def get_full_dir(dir):
        full_dir = os.path.normpath(blog_dir + '/' + dir)
        if (not os.path.exists(full_dir)):
            os.makedirs(full_dir)
        return full_dir

    def open_file(file):
        f = codecs.open(file, 'w', encoding='utf-8')
        return f

    def get_item_uid(item, date_prefix=False, namespace=''):
        result = None
        if namespace not in item_uids:
            item_uids[namespace] = {}

        if item['wp_id'] in item_uids[namespace]:
            result = item_uids[namespace][item['wp_id']]
        else:
            uid = []
            if (date_prefix):
                try:
                    dt = datetime.strptime(item['date'], date_fmt)
                except:
                    dt = datetime.today()
                    print 'Wrong date in', item['title']
                uid.append(dt.strftime('%Y-%m-%d'))
                uid.append('-')
            s_title = item['slug']
            if s_title is None or s_title == '':
                s_title = item['title']
            if s_title is None or s_title == '':
                s_title = 'untitled'
            s_title = s_title.replace(' ', '_')
            s_title = re.sub('[^a-zA-Z0-9_-]', '', s_title)
            uid.append(s_title)
            fn = ''.join(uid)
            n = 1
            while fn in item_uids[namespace]:
                n = n + 1
                fn = ''.join(uid) + '_' + str(n)
                item_uids[namespace][i['wp_id']] = fn
            result = fn
        return result

    def get_item_path(item, dir=''):
        full_dir = get_full_dir(dir)
        filename_parts = [full_dir, '/']
        filename_parts.append(item['uid'])
        if item['type'] == 'page':
            if (not os.path.exists(''.join(filename_parts))):
                os.makedirs(''.join(filename_parts))
            filename_parts.append('/index')
        filename_parts.append('.')
        filename_parts.append(target_format)
        return ''.join(filename_parts)

    def get_attachment_path(src, dir, dir_prefix='images'):
        try:
            files = attachments[dir]
        except KeyError:
            attachments[dir] = files = {}

        try:
            filename = files[src]
        except KeyError:
            file_root, file_ext = os.path.splitext(os.path.basename(
                urlparse(src)[2]))
            file_infix = 1
            if file_root == '':
                file_root = '1'
            current_files = files.values()
            maybe_filename = file_root + file_ext
            while maybe_filename in current_files:
                maybe_filename = file_root + '-' + str(file_infix) + file_ext
                file_infix = file_infix + 1
            files[src] = filename = maybe_filename

        target_dir = os.path.normpath(blog_dir + '/' + dir_prefix + '/' + dir)
        target_file = os.path.normpath(target_dir + '/' + filename)

        if (not os.path.exists(target_dir)):
            os.makedirs(target_dir)

        # if src not in attachments[dir]:
        #     print target_name
        return target_file

    for i in data['items']:
        skip_item = False

        for field, value in item_field_filter.iteritems():
            if(i[field] == value):
                skip_item = True
                break

        if(skip_item):
            continue

        sys.stdout.write('.')
        sys.stdout.flush()
        out = None
        try:
            date = datetime.strptime(i['date'], '%Y-%m-%d %H:%M:%S').replace(tzinfo=UTC())
        except:
            date = datetime.today()
            print 'Wrong date in', i['title']
        yaml_header = {
            'title': i['title'],
            'link': i['link'],
            'author': i['author'],
            'date': date,
            'slug': i['slug'],
            'wordpress_id': int(i['wp_id']),
            'comments': i['comments'],
        }
        if len(i['excerpt']) > 0:
            yaml_header['excerpt'] = i['excerpt']
        if i['status'] == u'publish':
            continue
        if i['status'] != u'publish':
            yaml_header['published'] = False

        if i['type'] == 'post':
            i['uid'] = get_item_uid(i, date_prefix=True)
            fn = get_item_path(i, dir='_posts')
            out = open_file(fn)
            yaml_header['layout'] = 'post'
        elif i['type'] == 'page':
            i['uid'] = get_item_uid(i)
            # Chase down parent path, if any
            parentpath = ''
            item = i
            while item['parent'] != '0':
                item = next((parent for parent in data['items']
                             if parent['wp_id'] == item['parent']), None)
                if item:
                    parentpath = get_item_uid(item) + '/' + parentpath
                else:
                    break
            fn = get_item_path(i, parentpath)
            out = open_file(fn)
            yaml_header['layout'] = 'page'
        elif i['type'] in item_type_filter:
            pass
        else:
            print 'Unknown item type :: ' + i['type']

        if download_images:
            for img in i['img_srcs']:
                try:
                    urlretrieve(urljoin(data['header']['link'],
                                        img.encode('utf-8')),
                                get_attachment_path(img, i['uid']))
                except:
                    print '\n unable to download ' + urljoin(
                        data['header']['link'], img.encode('utf-8'))

        if out is not None:
            def toyaml(data):
                return yaml.safe_dump(data, allow_unicode=True,
                                      default_flow_style=False).decode('utf-8')

            tax_out = {}
            for taxonomy in i['taxanomies']:
                for tvalue in i['taxanomies'][taxonomy]:
                    t_name = taxonomy_name_mapping.get(taxonomy, taxonomy)
                    if t_name not in tax_out:
                        tax_out[t_name] = []
                    if tvalue in tax_out[t_name]:
                        continue
                    tax_out[t_name].append(tvalue)

            out.write('---\n')
            if len(yaml_header) > 0:
                out.write(toyaml(yaml_header))
            if len(tax_out) > 0:
                out.write(toyaml(tax_out))

            out.write('---\n\n')
            try:
                out.write(html2fmt(i['body'], target_format))
            except:
                print '\n Parse error on: ' + i['title']

            out.close()
    print '\n'

wp_exports = glob(wp_exports + '/*.xml')
for wpe in wp_exports:
    data = parse_wp_xml(wpe)
    write_jekyll(data, target_format)

print 'done'

```