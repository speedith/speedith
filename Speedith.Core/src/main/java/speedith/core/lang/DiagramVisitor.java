/*
 *   Project: Speedith.Core
 * 
 * File name: DiagramVisitor.java
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
package speedith.core.lang;

import java.util.ArrayList;

/**
 * A {@link SpiderDiagram spider diagram} visitor whose methods are called when
 * traversing a spider diagram.
 *
 * @param <T> The type of the result that this visitor produces in the end.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public interface DiagramVisitor<T> {

    /**
     * This method is called by the visiting procedure before the first call to
     * the {@link DiagramVisitor#visit(speedith.core.lang.SpiderDiagram, int, int, java.util.LinkedList)
     * visit function} is made.
     *
     * @param root the diagram on which the visiting should happen.
     */
    void init(SpiderDiagram root);

    /**
     * This method is called by the visiting procedure just after the last call
     * to the {@link DiagramVisitor#visit(speedith.core.lang.SpiderDiagram, int, int, java.util.LinkedList)
     * visit function} and just before the {@link DiagramVisitor#getResult() }
     * will be called.
     */
    void end();

    /**
     * This function is called for every traversed sub-diagram of a root
     * diagram.
     *
     * @param subDiagram      the currently visited sub-diagram.
     * @param subDiagramIndex the index of the sub-diagram (relative to the
     *                        root).
     * @param parents         the parents of this sub-diagram (may be {@code null} to
     * @param childIndices    contains the child indices for the current diagram as
     *                        well as each parent. The value {@code childIndices.get(i)} is the
     *                        operand index at which parent {@code i + 1} appears within parent {@code i}.
     *                        The last value in this list is the operand index of the current spider
     *                        diagram within the last parent. The size of this list is the same as the
     *                        {@code parents} list. <span style="font-weight:bold">Note</span>:
     *                        this list is {@code null} exactly when the {@code parents} list is
     *                        {@code null}.
     * @param parentIndices
     */
    void visit(SpiderDiagram subDiagram, int subDiagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices, ArrayList<Integer> parentIndices);

    /**
     * Indicates that this visitor has done all the visiting it
     * intends to do.
     * <p>Once this method returns {@code true}, the visiting will stop. No more
     * calls to {@link DiagramVisitor#visit(speedith.core.lang.SpiderDiagram, int, int, java.util.LinkedList) the
     * visit function} will be made and the {@link DiagramVisitor#getResult()}
     * function can be called to retrieve the final result of the visit.</p>
     *
     * @return {@code true} if this visitor has no more visiting to do.
     */
    boolean isDone();

    /**
     * Returns the final result of the visit.
     *
     * @return the final result of the visit.
     */
    T getResult();
}
