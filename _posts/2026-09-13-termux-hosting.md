---
layout: post
title:  "Hosting Web Apps on Termux"
---

I read [Hacker News](https://news.ycombinator.com/) daily on my Android phone. To reduce my screen time, some of the articles are TTSed so I can listen to them. Here's the workflow:
1. I visit a [static website](https://heanyang1.github.io/vctb/hacker-news/index.html) to view HN posts and choose the articles to TTS.
2. Then I copy the URL of the articles to a note-taking app on my phone.
3. Once a week, I dump the URLs to my laptop and run a script that scrapes the webpages and convert the articles to audio using AI models like [kokoro](https://github.com/hexgrad/kokoro).

There are a lot of repetitive work here because the web page doesn't remember what I want to TTS later. Hosting a web app on the cloud isn't a good option neither since I don't want to pay for the server, and more importantly, I don't want someone hacking my web app and insert a malicious URL for my script to scrape.

Recently I have found a solution that fits the problem surprisingly well:
1. I host a web app on [Termux](https://termux.dev/en/) and view it in my phone's browser.
2. The app records the articles and store them on Termux.
3. I can also visit the app on my laptop to dump the URLs when they are connected to the same network. No manual copying needed.
4. It's safe as long as step 3 is done using my home's network, and I only allow my laptop to visit the site.

This post records the process of setting everything up.

## SSH into Termux

My phone is not suitable for programming tasks, so I need to SSH into Termux from my computer. The instructions of [this blog post](https://joeprevite.com/ssh-termux-from-computer) works for me.

## Install Pi Agent

Agents are useful when you have lots of things to install. I installed [Pi agent](https://pi.dev/) through `npm`:
```sh
pkg install npm
npm install -g --ignore-scripts @earendil-works/pi-coding-agent # or whatever on the official website
```

Pi recognizes that the environment is Termux, and will suggest you installing `ripgrep` using `pkg`.

## Aside: Python and Jupyter Notebook

Similar to the app I want to build, Jupyter Notebooks can also be hosted on Termux to provide a Python environment on Android phones. The problem is that many Python packages requires compiling C/C++/Rust code on Termux, and compiling requires lots of weird dependencies. Pure Python packages like Flask and Sympy can be installed via `pip`, and some well-known packages like Numpy or Matplotlib have system-wide packages [^name], and good luck if `pip` fails and you can't find the system package.

[^name]: The packages are usually called `python-[package name]`, e.g. Numpy's package is called `python-numpy`, but Matplotlib's package is called `matplotlib` which confuses the agent a lot.

After grinding for a long time, my agent managed to set up a Jupyter notebook server. After installing, running the command to start the server:
```sh
jupyter notebook password # set the password if you are using it the first time
jupyter notebook --no-browser
```

Then you have a nice Python environment on your phone:
![Jupyter notebook on my phone](/myblog/assets/2026-09-13/jupyter.png)
...except that most controls are broken because Jupyter notebook are not intended to be using on the phone. I'd rather use [J on Android](https://code.jsoftware.com/wiki/Guides/JAndroid) if there is something need to be calculated.

You can use it in other devices' browser though, by specifying `the phone's` IP address:
```sh
jupyter notebook --no-browser --ip=192.168.1.23 # use `ifconfig` to see your phone's address
```

So next time I visit my non-technical friend's home, I'll have something to play with instead of chatting embarrassingly. [^friend]

[^friend]: I think my non-technical friends will never invite me to their home after reading my blog.

## The App

Since it's a simple CRUD app that serves only one person, I use the simplest technology possible (Python+Flask+SQLite) and let my agent write the code. [The app itself](https://github.com/heanyang1/hn-viewer) is not interesting. What's interesting is that it runs anywhere, so I can write the app on my laptop and deploy it on my phone without changing anything.

## Future Work?

Now the app works and my TTS workflow is simplified, but I still have to dump it to my laptop to TTS. It will be better if the server also runs TTS models. It's not clear whether
- I can use GPU acceleration on Termux without root access
- My phone can run the models quickly enough without overheating
- The time (and token) spend to set things up worth the time saved

So I'll probably try it, but it's not on my top-priority todo list.

