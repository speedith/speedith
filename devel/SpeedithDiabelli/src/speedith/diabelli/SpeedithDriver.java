/*
 * File name: SpeedithDriver.java
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
package speedith.diabelli;

import diabelli.components.DiabelliComponent;
import diabelli.components.GoalAcceptingReasoner;
import diabelli.components.GoalProvidingReasoner;
import diabelli.logic.Goal;
import org.openide.util.lookup.ServiceProvider;

/**
 * This is the main class of the Speedith driver for Diabelli. It provides
 * current Speedith's goals to Diabelli and gives changed goals back to the
 * active Speedith proof script.
 *
 * <p>This driver also provides inference rule application functionality. This
 * means that a {@link Goal goal} can be given to this driver, it will present
 * it to the user, who will apply an inference rule on it, then the transformed
 * goal will be passed back to Diabelli, and finally back to the {@link GoalAcceptingReasoner goal-accepting reasoner}
 * to whom the initial goal belonged. </p>
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
@ServiceProvider(service = DiabelliComponent.class)
public class SpeedithDriver implements GoalProvidingReasoner {

    @Override
    public String getName() {
        return "Speedith";
    }
}
