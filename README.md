# Speedith

--------------------------------------------------------------------------------

Speedith is a diagrammatic theorem prover for [spider diagrams](http://en.wikipedia.org/wiki/Spider_diagram).



# Developer's Guide to _Speedith_ #

--------------------------------------------------------------------------------

## Using Speedith in Isabelle/HOL

*MixR* (the name of the Speedith/Isabelle integration) requires some special
settings for Isabelle. You can find sample settings in the Speedith
distribution's '`settings`' file.

You can either edit your existing Isabelle settings, or copy the included
'`devel/Theories/settings`' file to Isabelle's user settings folder (e.g.
'`~/.isabelle/Isabelle2011-1/etc/`').

--------------------------------------------------------------------------------

## Building and developing using IDEs

An easy way to build and develop Speedith is to install either
[NetBeans](http://netbeans.org/downloads/) or the
[Eclipse](http://www.eclipse.org/downloads/) IDEs.

In any case, you have to make sure that all of Speedith's dependencies are
installed (and configured in your IDE). You can find a list of dependencies in
the _Requirements_ section below.

Main development of Speedith is done in __NetBeans__. Eclipse is currently not
supported out of the box, but there is no technical reason why it would not work
(importing the Speedith's source folder should do the trick).

--------------------------------------------------------------------------------

## General Requirements

These requirements have to be checked only once. After you make sure you have
these, you can build Speedith at any time.

*   __Speedith sources__: You can get the sources of Speedith from
    [Gitorious](http://gitorious.org/speedith).

    You may simply want to execute this in the command line:

            git clone git://gitorious.org/speedith/speedith.git speedith
            cd speedith

*   __iCircles sources__: You can get the sources of iCircles from
    [Gitorious](http://gitorious.org/speedith/inductive_circles).

    You may simply want to execute this in the command line:

            git clone git://gitorious.org/speedith/inductive_circles.git inductive_circles
            cd inductive_circles

*   __Apache Ant__: Speedith can be built with [Ant](http://ant.apache.org/)
    (which is a Java-based build automation tool, similar to `make`). The
    minimum required version of Ant can be determined by running:

            grep 'antversion atleast=' devel/Speedith/nbproject/build-impl.xml

    You can install Ant via your operating system's package management system,
    or by downloading it from [http://ant.apache.org/bindownload.cgi](http://ant.apache.org/bindownload.cgi).

    Make sure that the `ant` executable is available from the command line in
    the root folder of Speedith (or make sure that you know where the `ant`
    executable is located).

    You can check your version of Ant by running:

            ant -version

*   __ANTLRv3__: Speedith uses the
    _[ANTLRv3 Java Runtime](http://www.antlr.org/download.html)_ for parsing the
    textual representation of spider diagrams.

    One way of getting ANTLRv3:

            wget 'http://www.antlr.org/download/antlr-3.3.tar.gz'
            tar -xzf antlr-3.3.tar.gz

    There should be the `./antlr-3.3/runtime/Java/target/antlr-runtime-3.3.jar` 
    file, which is the runtime library dependency required by Speedith. Also
    needed by Speedith is the `./antlr-3.3/lib/antlr-3.3-complete.jar` file, which
    is needed only during the compilation stage (not a runtime dependency).

*   __Apache Commons CLI__: Speedith uses [Apache Commons CLI](http://commons.apache.org/cli/)
    for command line parsing. You can download the library from [here](http://commons.apache.org/cli/download_cli.cgi).

    An example of how to get it with `wget`:

            wget 'http://mirror.lividpenguin.com/pub/apache//commons/cli/binaries/commons-cli-1.2-bin.tar.gz'
            tar -xzf commons-cli-1.2-bin.tar.gz

    The `./commons-cli-1.2/commons-cli-1.2.jar` is the file we're after.

--------------------------------------------------------------------------------

## Manual build process

__Note__: the instructions below assume the following:

*   the _current working directory_ is the __root of the Speedith repository__.
*   the `ant` executable is in your `PATH` environment variable.
*   the _iCircles_ sources are reachable via the `../inductive_circles` path.
    from the root of the Speedith repository.
*   you know the paths of `antlr-3.3-complete.jar`, `antlr-runtime-3.3.jar` and
    `commons-cli-1.2.jar` files (the instructions will use dummy paths).

To build and run Speedith, perform the following steps:

1.  Being in the repository's root folder, run:

            ../apache-ant-1.8.2/bin/ant --noconfig \
                -Dlibs.ANTLRv3.classpath=./antlr-3.3/runtime/Java/target/antlr-runtime-3.3.jar \
                -Dantlr3.tool.jar=./antlr-3.3/lib/antlr-3.3-complete.jar \
                -Dlibs.JakartaCLI.classpath=./commons-cli-1.2/commons-cli-1.2.jar \
                -f devel/Speedith/build.xml jar

2.  Run Speedith (again from the root folder of the `Speedith` repository):

            java -cp "./devel/Speedith.Core/dist/Speedith.Core.jar:./antlr-3.3/runtime/Java/target/antlr-runtime-3.3.jar:./commons-cli-1.2/commons-cli-1.2.jar:./devel/Speedith/dist/Speedith.jar:../inductive_circles/devel/iCircles/dist/iCircles.jar" speedith.Main




--------------------------------------------------------------------------------

# Building _MixR_ #

The Isabelle driver for MixR currently depends on _I3P_. The sources of the
I3P framework are available from [the I3P's official web
page](http://www-pu.informatik.uni-tuebingen.de/i3p/).

Note that all other MixR components do not depend on I3P, which makes them
usable in a plain NetBeans platform (without I3P modules).




--------------------------------------------------------------------------------

## Troubleshooting

### __Q1__: Speedith doesn't build. It fails with the following error `Problem: failed to create task or type antlib:org/apache/tools/ant/antlr:ant-antlr3`.

Your `Ant` tool is missing the `antlr3` task. You'll have to install it.

Under Ubuntu you'll have to download and extract the following file:

    [http://antlr.org/share/1169924912745/antlr3-task.zip](http://antlr.org/share/1169924912745/antlr3-task.zip)

Configure Ant to find the extracted `ant-antlr3.jar` file:

    ant -lib `path/to/ant-antlr3.jar`

The above file can also be found on [this list](http://antlr.org/share/list) (which is probably where updates should be posted).



--------------------------------------------------------------------------------

# Using _Hyperblocks_ #

The Blocksworld component requires an past version of JOGL (both the Java JAR
package and related platform-specific binaries). This can be obtained through
the installation package provided through Openbox. For example, the RPM package
`LPL-11_09-linux-rpm-installer.sh` will install the `jogl` binaries in the
folder `/usr/share/OP-jre/lib/i386/` (this folder must be placed into
`java.library.path` or you can create a symbolic link from one of the existing
empty folders in the path, for example `/usr/java/packages/lib/i386` on Fedora
16). To obtain the Java JAR `jogl.jar` package, contact
[Stanford CSLI](http://www-csli.stanford.edu/hp/).

Note that this works only with 32-bit versions of Java.

__Below are my notes from trying to make Hyperblocks work on a 64-bit Linux
machine. After trying for a while, I finally gave up. Maybe somebody will find
these notes useful:__

On 64-bit machines, one
also has to install the following packages:

-   `mesa-libGLU.i686`

## Getting JOGL from sources

If for some reason things keep failing, you might want to get JOGL yourself.

Since Hyperblocks uses an old version of JOGL (one that uses package names such
as `net.java.games.jogl`), you'll have to dig in the history of the [JOGL git
repository](http://kenai.com/projects/jogl/sources/jogl-git/content/src/net/java/games/jogl/DefaultGLCapabilitiesChooser.java?rev=8da5bfa2d72282bfdcd2889a70a93a4072221a1c).

To get the sources issue the following command:

    git clone git://kenai.com/jogl~jogl-git

It seems like the last revision before the merge of JSR-231 (which changed the
package names) was `42843c3290d64c41c9c8a18b93f5ad3c00d35ddc`.

Afterwards follow the guide `jogl~jogl-git/doc/HowToBuild.html` in the
repository.

If you are building on a 64-bit machine, open the `make/build.xml` file, find:

    <compiler id="compiler.cfg.linux" name="gcc">

and change it to:

    <compiler id="compiler.cfg.linux" name="gcc">
        <compilerarg value="-m32"/>
    </compiler>

### Notes

I had the following errors while trying to build JOGL:

1.  Error message:

            /home/matej/Documents/jogl~jogl-git/make/build.xml:1105: The following error occurred while executing this line:
            /home/matej/Documents/jogl~jogl-git/make/build.xml:866: The following error occurred while executing this line:
            /home/matej/Documents/jogl~jogl-git/make/build.xml:821: /usr/X11R6/lib does not exist.

    Solution:

    Replace every occurrence of `/usr/X11R6` into `/usr/lib`.

2.  Error message (probably only on 64-bit):

            /home/matej/Documents/jogl~jogl-git/make/build.xml:1105: The following error occurred while executing this line:
            /home/matej/Documents/jogl~jogl-git/make/build.xml:866: The following error occurred while executing this line:
            /home/matej/Documents/jogl~jogl-git/make/build.xml:821: /usr/lib/jvm/java-1.7.0-openjdk-1.7.0.3.x86_64/jre/lib/i386 does not exist.

    Solution:

    In the `jogl.properties` file set the `java.home.dir` to a 32-bit JVM:

        java.home.dir=/usr/lib/jvm/java-1.7.0-openjdk

3.  Error message (in C compilation stage):

                   [cc] In file included from /home/matej/Documents/jogl~jogl-git/src/native/jogl/JAWT_DrawingSurfaceInfo.c:40:0:
                   [cc] /usr/lib/jvm/java-1.7.0-openjdk/include/linux/jawt_md.h:31:27: fatal error: X11/Intrinsic.h: No such file or directory
                   [cc] compilation terminated.

            BUILD FAILED
            /home/matej/Documents/jogl~jogl-git/make/build.xml:1105: The following error occurred while executing this line:
            /home/matej/Documents/jogl~jogl-git/make/build.xml:866: The following error occurred while executing this line:
            /home/matej/Documents/jogl~jogl-git/make/build.xml:821: gcc failed with return code 1

    Solution:

    Install this:

            yum install libXt-devel.i686

4.  Message (and other similar ones):

            [cc] /usr/include/gnu/stubs.h:7:27: fatal error: gnu/stubs-32.h: No such file or directory
            [cc] compilation terminated.

    Solution: Install:

        yum install glibc-devel.i686

5.  Missing libraries (on a 64-bit machine):

            [cc] Starting link
            [cc] /usr/bin/ld: cannot find -lGL
            [cc] /usr/bin/ld: cannot find -lGLU
            [cc] /usr/bin/ld: skipping incompatible /usr/lib/jvm/java-1.7.0-openjdk/jre/lib/i386/libjawt.so when searching for -ljawt
            [cc] /usr/bin/ld: cannot find -ljawt
            [cc] /usr/bin/ld: skipping incompatible /usr/lib/libc.so when searching for -lc
            [cc] collect2: ld returned 1 exit status

    Solution:
