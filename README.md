# Speedith

--------------------------------------------------------------------------------

Speedith is a diagrammatic theorem prover for [spider diagrams](http://en.wikipedia.org/wiki/Spider_diagram).

[![Build Status](https://travis-ci.org/urbas/speedith.svg?branch=master)](https://travis-ci.org/urbas/speedith)




--------------------------------------------------------------------------------

# Developer's Guide to _Speedith_ #

--------------------------------------------------------------------------------

## General Requirements

These requirements have to be checked only once. After you make sure you have
these, you can build Speedith at any time.

*   Maven (see [installation instructions](https://maven.apache.org/))

*   Java 7: Currently, the project does not build against Java 8.

--------------------------------------------------------------------------------

## Building Speedith

Use Maven to build Speedith (in the root directory of your cloned Speedith repository):

    mvn install

--------------------------------------------------------------------------------

## Running Speedith

After a successful build, you can run Speedith through the following commands:

Windows 32-bit:

    export MAVEN_OPTS="-Djava.library.path=./win32-x86 -Djna.library.path=./win32-x86";
    mvn -pl Speedith.Gui exec:java -Dexec.mainClass=speedith.Main

Windows 64-bit:

    export MAVEN_OPTS="-Djava.library.path=./win32-x86-64 -Djna.library.path=./win32-x86-64";
    mvn -pl Speedith.Gui exec:java -Dexec.mainClass=speedith.Main