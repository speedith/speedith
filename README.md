# Speedith

--------------------------------------------------------------------------------

Speedith is a diagrammatic theorem prover for [spider diagrams](http://en.wikipedia.org/wiki/Spider_diagram).




--------------------------------------------------------------------------------

# Developer's Guide to _Speedith_ #

--------------------------------------------------------------------------------

## General Requirements

These requirements have to be checked only once. After you make sure you have
these, you can build Speedith at any time.

*   __iCircles sources__: You can get the sources of iCircles from
    [GitHub](https://github.com/urbas/iCircles).

    You may simply want to execute this in the command line:

            git clone https://github.com/urbas/iCircles.git
            cd iCircles
            mvn install

*   __Propity Library__: You can get the sources from
    [GitHub](https://github.com/urbas/mixr).

    Execute this in the command line:

            git clone https://github.com/urbas/mixr.git
            cd mixr/Propity
            mvn install

--------------------------------------------------------------------------------

## Building Speedith

Use Maven to build Speedith (in the root directory of your cloned Speedith repository):

    mvn install

--------------------------------------------------------------------------------

## Running Speedith

After a successful build, you can run Speedith by firstly entering the `Speedith.Gui` directory:

    cd Speedith.Gui

and then running:

    mvn exec:java -Dexec.mainClass=speedith.Main

--------------------------------------------------------------------------------

## Using Speedith in Isabelle/HOL

*MixR* (the name of the Speedith/Isabelle integration) requires some special
settings for Isabelle. You can find sample settings in the Speedith
distribution's '`settings`' file.

You can either edit your existing Isabelle settings, or copy the included
'`devel/Theories/settings`' file to Isabelle's user settings folder (e.g.
'`~/.isabelle/Isabelle2011-1/etc/`').
