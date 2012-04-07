/*
 * File name: IsabelleDriver.java
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
package diabelli.isabelle;

import diabelli.Diabelli;
import diabelli.GoalManager;
import diabelli.components.DiabelliComponent;
import diabelli.components.GoalAcceptingReasoner;
import java.util.logging.Level;
import java.util.logging.Logger;
import org.openide.util.Lookup;
import org.openide.util.lookup.ServiceProvider;

/**
 * This is the main class of the Isabelle driver for Diabelli. It provides
 * current Isabelle's goals to Diabelli and gives changed goals back to the
 * active Isabelle script.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
@ServiceProvider(service = DiabelliComponent.class)
public class IsabelleDriver implements GoalAcceptingReasoner {

    public IsabelleDriver() {
        Logger.getLogger(IsabelleDriver.class.getName()).log(Level.INFO, "Diabelli Isabelle Driver initialised.");
        Diabelli diabelli = Lookup.getDefault().lookup(Diabelli.class);
        GoalManager goalManager = diabelli.getGoalManager();
        Logger.getLogger(IsabelleDriver.class.getName()).log(Level.INFO, "Got goal manager: {0}", goalManager.toString());
    }

    @Override
    public String getName() {
        return org.openide.util.NbBundle.getBundle(IsabelleDriver.class).getString("ISA_DRIVER_NAME");
    }
}
