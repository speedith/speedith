/*
 * File name: GoalBasedReasoner.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
 * 
 *  Copyright © 2012 Matej Urbas
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package diabelli.components;

/**
 * Goal-based reasoners are all interactive reasoners that fulfil the following
 * requirements: <ul> <li>a list of goals to be proved should be provided
 * (these goals may be provided to the Diabelli framework in whatever format,
 * but the format should preferably be understandable by other Diabelli
 * components, which could then present these goals diagrammatically for
 * example),</li> <li>the goals should contain premises and a conclusion (a goal
 * is proved if the premises entail the conclusion trivially), and</li> <li>if
 * the list of goals changes, Diabelli should be notified of it (through
 * events).</li> </ul>
 * 
 * <p>Note that a goal-based reasoner alone does not have to accept changed
 * goals from other components. Goal-based reasoners can use the Diabelli
 * framework merely for displaying goals in other ways (diagrammatic, for example)
 * or exporting them to other components. Reasoners that accept changed goals
 * are of the type {@link GoalAcceptingReasoner}.</p>
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public interface GoalBasedReasoner extends Reasoner {
    
}
