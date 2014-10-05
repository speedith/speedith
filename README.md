# Speedith

--------------------------------------------------------------------------------

Speedith is a diagrammatic theorem prover for [spider diagrams](http://en.wikipedia.org/wiki/Spider_diagram).




--------------------------------------------------------------------------------

# Developer's Guide to _Speedith_ #

--------------------------------------------------------------------------------

## General Requirements

These requirements have to be checked only once. After you make sure you have
these, you can build Speedith at any time.

*   Java 7: Currently, the project does not build against Java 8.

--------------------------------------------------------------------------------

## Building Speedith

Use Maven to build Speedith (in the root directory of your cloned Speedith repository):

    mvn install

--------------------------------------------------------------------------------

## Running Speedith

After a successful build, you can run Speedith through the following command:

    mvn -pl Speedith.Gui exec:java -Dexec.mainClass=speedith.Main