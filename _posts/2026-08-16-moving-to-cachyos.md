---
layout: post
title:  "Moving to CachyOS"
---

I've been using i3 on Debian and Arch Linux for many years on my old laptop. Despite some weird issues caused by not having a desktop environment, the system is pretty stable. Last year, however, I bought a new laptop with a new Nvidia graphics card and immediately went into trouble:
- I wanted to install Arch since it has the latest Nvidia driver available, but `iwd` in the Arch installer is not able to turn my exotic Wi-Fi device on.
- Then I tried Manjaro, which has a graphical installer that managed to connect to the network. I don't like its i3 config, so I installed the Xfce version and configured i3 manually.
- The system works fine in cold days, but when summer came, it starts to overheated and occasionally shut down (probably because of some problem regulating the fan speed). 
- Finally, it's overheated and turned off during a `pacman` session this week, making the system unbootable.

Instead of trying to recover from the mess, I decided to pack things up and switch to a new distro. I'm moving to [CachyOS](https://cachyos.org/) because
- It's Arch-based
- There is a installer that recognizes my weird hardware
- It has (somewhat) out-of-box configuration for [tiling window managers](https://wiki.archlinux.org/title/Window_manager#Tiling_window_managers) like Hyprland, i3 and sway
- The kernel and some packages are optimized for performance

Here's a screenshot taken when writing this blog:
![final](/myblog/assets/2026-08-16/final.png)

This post records the process of me installing and configuring the OS.

## Installer

The disk partitioning part is not very helpful. None of the options except `Erase disk` and `Manual partitioning` can install a bootable OS, and I need to allocate some swap spaces since the laptop only has 16GB of memory and memory prices are high.
![install](/myblog/assets/2026-08-16/install.png)

## Temperature

It's raining these days and the temperature is lower than \(30^{\circ}\text{C}\), so I don't have the chance to test whether the system can manage its fans properly to avoid overheating. I'll update this post if it fails.

## Hyprland

I didn't remember why I didn't use i3 or sway in the end and I don't want to reinstall it to find out. Maybe there is no Wi-Fi icon on the status bar and I have to use `iwd` to change Wi-Fi. I'm using Hyprland anyway.

CachyOS has [Noctalia](https://noctalia.dev/) shipped with Hyprland. It looks like a bunch of utils similar to `i3bar`, `dmenu`, etc. and contains too many features not needed, but it's useable and not get in my way often, so I'll keep using it.

So far I've only tinkered with the Noctalia's GUI settings and changed some config.

Key bindings are changed to be consistent with i3:
```lua
-- ~/.config/hypr/config/binds.lua
hl.bind(mainMod .. " + SHIFT + Q",   hl.dsp.window.close())
hl.bind(mainMod .. " + H",           hl.dsp.focus({ direction = "left" }))
hl.bind(mainMod .. " + J",           hl.dsp.focus({ direction = "down" }))
hl.bind(mainMod .. " + K",           hl.dsp.focus({ direction = "up" }))
hl.bind(mainMod .. " + L",           hl.dsp.focus({ direction = "right" }))
-- ...
```
and the margins are removed to make use of the screen space:
```lua
-- ~/.config/hypr/config/decorations.lua
hl.config({
    general = {
        gaps_in = 0,
        gaps_out = 1,
        border_size = 3,
        extend_border_grab_area = 10,
        resize_on_border = true,
        -- ...
    },
    -- ...
})
```

## Firewall

I'm using LAN file transfer software like [KDE Connect](https://community.kde.org/KDEConnect) and [LocalSend](https://localsend.org/), and according to [this thread](https://discuss.cachyos.org/t/kdeconnect-not-connecting/2359), I have to configure the firewall to make them work:
```sh
sudo ufw allow 1714:1764 # for KDE Connect
sudo ufw allow 53317 # for Localsend
sudo ufw reload
```

## Outro

So far I'm satisfied with the OS and configuration. I'll try to tinker with Hyprland to increase my productivity or just for fun. Hopefully this system will not be blown up like the previous one.

Beside moving to a new distro, I'm also moving physically to a new house, so I don't have much time for writing. I'll continue the static analysis series once I settle down.

