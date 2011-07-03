/*
 *   Project: Speedith.Core
 * 
 * File name: Transformer.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
 * 
 *  Copyright © 2011 Matej Urbas
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

import java.util.LinkedList;

/**
 * Transformers operate on spider diagrams via the {@link
 * SpiderDiagram#transform(speedith.core.lang.Transformer) transform method}.
 * <p>The {@link
 * SpiderDiagram#transform(speedith.core.lang.Transformer) transform method}
 * traverses the spider diagram and applies the {@link Transformer
 * transformer's} {@link Transformer#transform(speedith.core.lang.CompoundSpiderDiagram, int, int, java.util.LinkedList)
 * transform method} for every nested spider diagram and at the same time
 * constructs the transformed spider diagram, which will be the result of the
 * whole operation.</p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public interface Transformer {
    /**
     * This function is called by the spider diagrams' {@link
     * SpiderDiagram#transform(speedith.core.lang.Transformer) transform
     * method} while it traverses the spider diagram expression tree.
     * <p>This function takes a spider diagram (that is currently traversed) and
     * returns either:
     *  <ul>
     *      <li>a new spider diagram,</li>
     *      <li>{@code null}, or</li>
     *      <li>the one it got as an input argument.</li>
     *  </ul>
     * </p>
     * <p>The calling <span style="font-style:italic;">transform</span> method
     * will perform one of the following for each of the above cases
     * (respectively):
     *  <ul>
     *      <li>exchange the returned spider diagram with the visited one and
     *          will continue with its next sibling/uncle etc. This means that
     *          the calling <span style="font-style:italic;">transform</span>
     *          method will not descend into the returned spider diagram,</li>
     *      <li>ignores the returned {@code null} value and descends into the
     *          input argument spider diagram (if it is a compound spider
     *          diagram), or</li>
     *      <li>ignores the same spider diagram and continues with the next
     *          sibling/uncle etc.</li>
     *  </ul>
     * </p>
     * <p>Immediately after the above the calling
     * <span style="font-style:italic;">transform</span> method calls the {@link
     * Transformer transformer's} {@link Transformer#isDone()} method. If the
     * latter returns {@code null}, the whole transformation process stops (no
     * more descends are made and the final transformed spider diagram is
     * constructed).</p>
     * @param sd the current spider diagram to transform.
     * @param diagramIndex the sub-diagram index of the current spider diagram.
     * @param childIndex the child index of this spider diagram (if it has a
     * compound spider diagram parent).
     * @param parents the stack of parents (if any).
     * <span style="font-weight:bold">Note</span>: this value might be {@code
     * null} or empty, which indicates that the current spider diagram does not
     * have any parents.
     * @return a transformed spider diagram, {@code null}, or the same spider
     * diagram as was given as the input argument.
     * @throws TransformationException thrown if the transformation failed for
     * any reason.
     */
    public SpiderDiagram transform(PrimarySpiderDiagram sd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) throws TransformationException;
    /**
     * This function is called by the spider diagrams' {@link
     * SpiderDiagram#transform(speedith.core.lang.Transformer) transform
     * method} while it traverses the spider diagram expression tree.
     * <p>This function takes a spider diagram (that is currently traversed) and
     * returns either:
     *  <ul>
     *      <li>a new spider diagram,</li>
     *      <li>{@code null}, or</li>
     *      <li>the one it got as an input argument.</li>
     *  </ul>
     * </p>
     * <p>The calling <span style="font-style:italic;">transform</span> method
     * will perform one of the following for each of the above cases
     * (respectively):
     *  <ul>
     *      <li>exchange the returned spider diagram with the visited one and
     *          will continue with its next sibling/uncle etc. This means that
     *          the calling <span style="font-style:italic;">transform</span>
     *          method will not descend into the returned spider diagram,</li>
     *      <li>ignores the returned {@code null} value and descends into the
     *          input argument spider diagram (if it is a compound spider
     *          diagram), or</li>
     *      <li>ignores the same spider diagram and continues with the next
     *          sibling/uncle etc.</li>
     *  </ul>
     * </p>
     * <p>Immediately after the above the calling
     * <span style="font-style:italic;">transform</span> method calls the {@link
     * Transformer transformer's} {@link Transformer#isDone()} method. If the
     * latter returns {@code null}, the whole transformation process stops (no
     * more descends are made and the final transformed spider diagram is
     * constructed).</p>
     * @param sd the current spider diagram to transform.
     * @param diagramIndex the sub-diagram index of the current spider diagram.
     * @param childIndex the child index of this spider diagram (if it has a
     * compound spider diagram parent).
     * @param parents the stack of parents (if any).
     * <span style="font-weight:bold">Note</span>: this value might be {@code
     * null} or empty, which indicates that the current spider diagram does not
     * have any parents.
     * @return a transformed spider diagram, {@code null}, or the same spider
     * diagram as was given as the input argument.
     * @throws TransformationException thrown if the transformation failed for
     * any reason.
     */
    public SpiderDiagram transform(NullSpiderDiagram sd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) throws TransformationException;
    /**
     * This function is called by the spider diagrams' {@link
     * SpiderDiagram#transform(speedith.core.lang.Transformer) transform
     * method} while it traverses the spider diagram expression tree.
     * <p>This function takes a spider diagram (that is currently traversed) and
     * returns either:
     *  <ul>
     *      <li>a new spider diagram,</li>
     *      <li>{@code null}, or</li>
     *      <li>the one it got as an input argument.</li>
     *  </ul>
     * </p>
     * <p>The calling <span style="font-style:italic;">transform</span> method
     * will perform one of the following for each of the above cases
     * (respectively):
     *  <ul>
     *      <li>exchange the returned spider diagram with the visited one and
     *          will continue with its next sibling/uncle etc. This means that
     *          the calling <span style="font-style:italic;">transform</span>
     *          method will not descend into the returned spider diagram,</li>
     *      <li>ignores the returned {@code null} value and descends into the
     *          input argument spider diagram (if it is a compound spider
     *          diagram), or</li>
     *      <li>ignores the same spider diagram and continues with the next
     *          sibling/uncle etc.</li>
     *  </ul>
     * </p>
     * <p>Immediately after the above the calling
     * <span style="font-style:italic;">transform</span> method calls the {@link
     * Transformer transformer's} {@link Transformer#isDone()} method. If the
     * latter returns {@code null}, the whole transformation process stops (no
     * more descends are made and the final transformed spider diagram is
     * constructed).</p>
     * @param sd the current spider diagram to transform.
     * @param diagramIndex the sub-diagram index of the current spider diagram.
     * @param childIndex the child index of this spider diagram (if it has a
     * compound spider diagram parent).
     * @param parents the stack of parents (if any).
     * <span style="font-weight:bold">Note</span>: this value might be {@code
     * null} or empty, which indicates that the current spider diagram does not
     * have any parents.
     * @return a transformed spider diagram, {@code null}, or the same spider
     * diagram as was given as the input argument.
     * @throws TransformationException thrown if the transformation failed for
     * any reason.
     */
    public SpiderDiagram transform(CompoundSpiderDiagram sd, int diagramIndex, int childIndex, LinkedList<CompoundSpiderDiagram> parents) throws TransformationException;
    /**
     * Indicates that this transformer has done all the transformations it
     * intends to do.
     * <p>Once this method returns {@code true}, the transformation will. All
     * the transformations done so far will be applied in the resulting
     * spider diagram.</p>
     * @return {@code true} if this transformer has no more transformations to
     * do.
     */
    public boolean isDone();
}
