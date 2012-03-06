/*
 *   Project: Speedith
 * 
 * File name: SelectionStep.java
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
package speedith.ui.selection;

import java.util.Locale;
import speedith.i18n.Translations;
import speedith.ui.SpiderDiagramClickEvent;
import static speedith.i18n.Translations.*;
import speedith.ui.SpiderDiagramPanel;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public abstract class SelectionStep {

    /**
     * This class provides an explanation on why a click was rejected in {@link 
     * SelectionStep#acceptClick(speedith.ui.SpiderDiagramClickEvent, speedith.ui.selection.SelectionSequence, int) }.
     *  <p>To issue a rejection without an explanation, you may want to use
     * {@link SelectionStep#EmptyClickRejection}.</p>
     */
    public static class ClickRejectionExplanation {

        /**
         * Returns the internationalise explanation of the rejection in {@link 
         * SelectionStep#acceptClick(speedith.ui.SpiderDiagramClickEvent, speedith.ui.selection.SelectionSequence, int) }.
         * @return the internationalise explanation of the rejection in {@link 
         * SelectionStep#acceptClick(speedith.ui.SpiderDiagramClickEvent, speedith.ui.selection.SelectionSequence, int) }.
         */
        public String getExplanation() {
            return this.getExplanation(Locale.getDefault());
        }

        /**
         * Returns the internationalise explanation of the rejection in {@link 
         * SelectionStep#acceptClick(speedith.ui.SpiderDiagramClickEvent, speedith.ui.selection.SelectionSequence, int) }.
         * @param locale the locale in which to return the explanation message.
         * @return the internationalise explanation of the rejection in {@link 
         * SelectionStep#acceptClick(speedith.ui.SpiderDiagramClickEvent, speedith.ui.selection.SelectionSequence, int) }.
         */
        public String getExplanation(Locale locale) {
            return null;
        }
    }
    
    public static class I18NClickRejectionExplanation extends ClickRejectionExplanation {
        private final String i18nKey;
        private final Object[] i18nStrArgs;

        /**
         * Creates an internationalised explanation of the click rejection.
         * @param i18nKey the internationalisation key to use for the message. It
         * will be looked up through {@link Translations#i18n(java.lang.String)}.
         * @param i18nStrArgs the internationalisation arguments (may be {@code null}). 
         */
        public I18NClickRejectionExplanation(String i18nKey, Object[] i18nStrArgs) {
            this.i18nKey = i18nKey;
            this.i18nStrArgs = i18nStrArgs;
        }

        /**
         * Creates an internationalised explanation of the click rejection.
         * @param i18nKey the internationalisation key to use for the message. It
         * will be looked up through {@link Translations#i18n(java.lang.String)}.
         */
        public I18NClickRejectionExplanation(String i18nKey) {
            this(i18nKey, null);
        }

        @Override
        public String getExplanation(Locale locale) {
            return i18nStrArgs == null ? i18n(locale, i18nKey) : i18n(locale, i18nKey, i18nStrArgs);
        }
        
    }
    
    /**
     * This object may be used to reject a click in {@link SelectionStep#acceptClick(speedith.ui.SpiderDiagramClickEvent, speedith.ui.selection.SelectionSequence, int) }
     * without an explanation.
     */
    public static final ClickRejectionExplanation EmptyClickRejection = new ClickRejectionExplanation();
    
//    /**
//     * This function is called before the first click happens (i.e. before the
//     * first call to the {@link SelectionStep#acceptClick(speedith.ui.SpiderDiagramClickEvent)}
//     * function) or when the user presses  the "Previous" button and ends up on
//     * this step.
//     *  <p>This function is also called when the user hits the <span
//     * style="font-style:italic;">previous</span> button and this brings the
//     * user back to this selection step.</p>
//     * @param selection the selection sequence in which this selection step
//     * participates. This object contains currently {@link SelectionStep#acceptClick(speedith.ui.SpiderDiagramClickEvent)
//     * approved} selections.
//     * @param thisIndex the index of this step in the given {@link SelectionSequence}.
//     */
//    public abstract void init(SelectionSequence selection, int thisIndex);
    
    /**
     * Indicates whether this selection step is finished. If it is, then the
     * user interface must proceed to the next step.
     * <p>This value can change only after the calls to {@link
     * SelectionStep#acceptClick(speedith.ui.SpiderDiagramClickEvent)} and {@link
     * SelectionStep#init(speedith.ui.selection.SelectionSequence, int)}. The user
     * interface will acceptClick this function before the first click event in this
     * step and after every click event (i.e. after every call to the {@link SelectionStep#acceptClick(speedith.ui.SpiderDiagramClickEvent)}
     * function).</p>
     * @param selection a list of selection steps and their accepted clicks.
     * @param thisIndex the index of this step within the selection sequence.
     * @return a value that indicates whether this selection step is finished.
     */
    public abstract boolean isFinished(SelectionSequence selection, int thisIndex);
    
    /**
     * Returns a value that indicates whether this step can be skipped.
     * <p>This value can change only after the calls to {@link
     * SelectionStep#acceptClick(speedith.ui.SpiderDiagramClickEvent)} and {@link
     * SelectionStep#init(speedith.ui.selection.SelectionSequence, int)}. The user
     * interface will acceptClick this function before the first click event in this
     * step and after every click event (i.e. after every call to the {@link SelectionStep#acceptClick(speedith.ui.SpiderDiagramClickEvent)}
     * function).</p>
     * @param selection a list of selection steps and their accepted clicks.
     * @param thisIndex the index of this step within the selection sequence.
     * @return a value that indicates whether this step can be skipped.
     */
    public abstract boolean isSkippable(SelectionSequence selection, int thisIndex);
    
    /**
     * Returns an internationalised instructional message for the user. This
     * message contains human-readable instructions on what elements to select
     * and how.
     * @return an internationalised instructional message for the user.
     */
    public String getInstruction() {
        return this.getInstruction(Locale.getDefault());
    }
    
    /**
     * Returns an internationalised instructional message for the user. This
     * message contains human-readable instructions on what elements to select
     * and how.
     * @param locale the locale in which to return the internationalised message.
     * @return an internationalised instructional message for the user.
     */
    public abstract String getInstruction(Locale locale);
    
    /**
     * This method is invoked by the {@link ElementSelectionDialog element
     * selection dialog} whenever the user clicks on the diagram.
     * <p>If this method returns {@code null} then the click is accepted and
     * is added to the list of accepted click events of this step in the given {@link SelectionSequence
     * selection sequence}. If any non-{@code null} value is returned, the click
     * is rejected and a message is displayed to the user.</p>
     * @param event the click event to accept or reject.
     * @param selection a list of selection steps and their accepted clicks.
     * @param thisIndex the index of this step within the selection sequence.
     * @return {@code null} if the click should be accepted, and a non-{@code null}
     * value if the click should be rejected. In the latter case the returned
     * object should also contain a message explaining the reason for rejection.
     */
    public abstract ClickRejectionExplanation acceptClick(SpiderDiagramClickEvent event, SelectionSequence selection, int thisIndex);
    
    /**
     * This method indicates whether the selection sequence UI should clean
     * all the selection of this step when the user presses the "previous" button.
     * @return a value that indicates whether the selection sequence UI should clean
     * all the selection of this step when the user presses the "previous" button.
     */
    public abstract boolean cleanSelectionOnStart();
    
    /**
     * Returns a value that indicates which elements of the diagram should be
     * highlighted (for selection).
     *  <p>For a set of possible values see: {@link SpiderDiagramPanel#setHighlightMode(int) }.</p>
     * @return
     */
    public abstract int getHighlightingMode();
}
