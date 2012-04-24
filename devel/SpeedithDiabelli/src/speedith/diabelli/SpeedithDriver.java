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

import speedith.diabelli.logic.IsabelleToSpidersTranslator;
import speedith.diabelli.logic.SpeedithFormatDescriptor;
import diabelli.components.DiabelliComponent;
import diabelli.components.FormulaFormatsProvider;
import diabelli.components.FormulaTranslationsProvider;
import diabelli.components.GoalAcceptingReasoner;
import diabelli.components.util.BareGoalProvidingReasoner;
import diabelli.logic.FormulaFormat;
import diabelli.logic.FormulaFormatDescriptor;
import diabelli.logic.FormulaTranslator;
import diabelli.logic.Goal;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
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
public class SpeedithDriver extends BareGoalProvidingReasoner implements FormulaFormatsProvider, FormulaTranslationsProvider {

    @Override
    public String getName() {
        return "Speedith";
    }
    
    // <editor-fold defaultstate="collapsed" desc="Formula Format Provider">
    @Override
    public Collection<FormulaFormat<?>> getFormulaFormats() {
        return FormulaFormatsContainer.SpeedithFormats;
    }
    
    private static class FormulaFormatsContainer {
        private static final List<FormulaFormat<?>> SpeedithFormats;
        
        static {
            ArrayList<FormulaFormat<?>> tmp = new ArrayList<>();
            tmp.add(SpeedithFormatDescriptor.getInstance());
            SpeedithFormats = Collections.unmodifiableList(tmp);
        }
    }
    // </editor-fold>

    //<editor-fold defaultstate="collapsed" desc="Formula Translations Provider">
    @Override
    public Collection<FormulaTranslator<?, ?>> getFormulaTranslators() {
        return FormulaTranslatorsContainer.SpeedithTranslator;
    }
    
    private static class FormulaTranslatorsContainer {
        private static final List<FormulaTranslator<?, ?>> SpeedithTranslator;
        
        static {
            ArrayList<FormulaTranslator<?, ?>> tmp = new ArrayList<>();
            tmp.add(IsabelleToSpidersTranslator.getInstance());
            SpeedithTranslator = Collections.unmodifiableList(tmp);
        }
    }
    //</editor-fold>
}
