#!/bin/bash

# cd to build directory

if [ "$1" = "config" ]; then
    ../configure                                     \
          --audio-drv-list=                                           \
          --disable-sdl                                               \
          --disable-gtk                                               \
          --disable-vte                                               \
          --disable-opengl                                            \
          --disable-virglrenderer                                     \
          --target-list=x86_64-linux-user,x86_64-softmmu              \
          --enable-debug                                              \
          --disable-werror                                            \
          --disable-kvm \
          --enable-debug-tcg
fi

make -j64