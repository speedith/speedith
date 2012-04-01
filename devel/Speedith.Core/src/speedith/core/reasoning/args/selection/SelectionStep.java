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
package speedith.core.reasoning.args.selection;

import java.util.Locale;
import speedith.core.reasoning.args.RuleArg;

/**
 * This class is used in {@link DiagramSelectionDialog} and {@link ElementSelectionPanel}
 * to guide the user through the diagram element selection and also make sure
 * that the exact selection is made.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public abstract class SelectionStep {

    // <editor-fold defaultstate="collapsed" desc="Public Constants">
    /**
     * This flag is used in {@link SelectionStep#getSelectableElements()} to
     * indicate which diagram elements should be selectable. <p>In this case
     * <span style="font-style:italic;">nothing</span> should be selectable.</p>
     */
    public static final int None = 0;
    /**
     * This flag is used in {@link SelectionStep#getSelectableElements()} to
     * indicate which diagram elements should be selectable. <p>In this case
     * <span style="font-style:italic;">spiders</span> should be selectable.</p>
     */
    public static final int Spiders = 0x1;
    /**
     * This flag is used in {@link SelectionStep#getSelectableElements()} to
     * indicate which diagram elements should be selectable. <p>In this case
     * <span style="font-style:italic;">zones</span> should be selectable.</p>
     */
    public static final int Zones = 0x2;
    /**
     * This flag is used in {@link SelectionStep#getSelectableElements()} to
     * indicate which diagram elements should be selectable. <p>In this case
     * <span style="font-style:italic;">contours</span> should be
     * selectable.</p>
     */
    public static final int Contours = 0x4;
    /**
     * This flag is used in {@link SelectionStep#getSelectableElements()} to
     * indicate which diagram elements should be selectable. <p>In this case
     * <span style="font-style:italic;">all elements of primary spider
     * diagrams</span> should be selectable.</p>
     */
    public static final int AllPrimaryElements = Spiders | Zones | Contours;
    /**
     * This flag is used in {@link SelectionStep#getSelectableElements()} to
     * indicate which diagram elements should be selectable. <p>In this case
     * <span style="font-style:italic;">operators of compound spider
     * diagrams</span> should be selectable.</p>
     */
    public static final int Operators = 0x8;
    /**
     * This flag is used in {@link SelectionStep#getSelectableElements()} to
     * indicate which diagram elements should be selectable. <p>In this case
     * <span style="font-style:italic;">null spider diagrams</span> should be
     * selectable.</p>
     */
    public static final int NullSpiderDiagrams = 0x10;
    /**
     * This flag is used in {@link SelectionStep#getSelectableElements()} to
     * indicate which diagram elements should be selectable. <p>In this case
     * <span style="font-style:italic;">everything</span> should be
     * selectable.</p>
     */
    public static final int All = Spiders | Zones | Contours | Operators | NullSpiderDiagrams;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Rejection Explanation Classes">
    /**
     * This class provides an explanation on why a click was rejected in {@link
     * SelectionStep#acceptSelection(speedith.ui.SpiderDiagramClickEvent, speedith.ui.selection.SelectionSequence, int)
     * }. <p>To issue a rejection without an explanation, you may want to use
     * {@link SelectionStep#EmptyClickRejection}.</p>
     */
    public static class SelectionRejectionExplanation {

        /**
         * Returns the internationalise explanation of the rejection in {@link
         * SelectionStep#acceptSelection(speedith.ui.SpiderDiagramClickEvent, speedith.ui.selection.SelectionSequence, int)
         * }.
         *
         * @return the internationalise explanation of the rejection in {@link
         * SelectionStep#acceptSelection(speedith.ui.SpiderDiagramClickEvent, speedith.ui.selection.SelectionSequence, int)
         * }.
         */
        public String getExplanation() {
            return this.getExplanation(Locale.getDefault());
        }

        /**
         * Returns the internationalise explanation of the rejection in {@link
         * SelectionStep#acceptSelection(speedith.ui.SpiderDiagramClickEvent, speedith.ui.selection.SelectionSequence, int)
         * }.
         *
         * @param locale the locale in which to return the explanation message.
         * @return the internationalise explanation of the rejection in {@link
         * SelectionStep#acceptSelection(speedith.ui.SpiderDiagramClickEvent, speedith.ui.selection.SelectionSequence, int)
         * }.
         */
        public String getExplanation(Locale locale) {
            return null;
        }
    }

    public static class I18NSelectionRejectionExplanation extends SelectionRejectionExplanation {

        private final String i18nKey;
        private final Object[] i18nStrArgs;

        /**
         * Creates an internationalised explanation of the click rejection.
         *
         * @param i18nKey the internationalisation key to use for the message.
         * It will be looked up through {@link Translations#i18n(java.lang.String)}.
         * @param i18nStrArgs the internationalisation arguments (may be {@code null}).
         */
        public I18NSelectionRejectionExplanation(String i18nKey, Object[] i18nStrArgs) {
            this.i18nKey = i18nKey;
            this.i18nStrArgs = i18nStrArgs;
        }

        /**
         * Creates an internationalised explanation of the click rejection.
         *
         * @param i18nKey the internationalisation key to use for the message.
         * It will be looked up through {@link Translations#i18n(java.lang.String)}.
         */
        public I18NSelectionRejectionExplanation(String i18nKey) {
            this(i18nKey, null);
        }

        @Override
        public String getExplanation(Locale locale) {
            return i18nStrArgs == null ? speedith.core.i18n.Translations.i18n(locale, i18nKey) : speedith.core.i18n.Translations.i18n(locale, i18nKey, i18nStrArgs);
        }
    }
    /**
     * This object may be used to reject a click in {@link SelectionStep#acceptSelection(speedith.ui.SpiderDiagramClickEvent, speedith.ui.selection.SelectionSequence, int)
     * }
     * without an explanation.
     */
    public static final SelectionRejectionExplanation EmptyClickRejection = new SelectionRejectionExplanation();
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    /**
     * This function is called at the start of this step. Still, the selection
     * might already contain some elements. This method should check it and
     * produce an explanation if the elements do not adhere to the requirements
     * of this step. Otherwise, if everything is alright, this method should
     * simply return {@code null}. <p>This function is also called when the user
     * hits the <span style="font-style:italic;">previous</span> button and this
     * brings the user back to this selection step.</p>
     *
     * @param selection the selection sequence in which this selection step
     * participates. This object contains currently {@link SelectionStep#acceptSelection(speedith.ui.SpiderDiagramClickEvent)
     * approved} selections.
     * @param thisIndex the index of this step in the given {@link SelectionSequence}.
     * @return {@code null} if the selection is valid, and a non-{@code null}
     * object otherwise.
     */
    public abstract SelectionRejectionExplanation init(SelectionSequence selection, int thisIndex);

    /**
     * Indicates whether this selection step is finished. If it is, then the
     * user interface must proceed to the next step. <p>This value can change
     * only after the calls to {@link
     * SelectionStep#acceptSelection(speedith.ui.SpiderDiagramClickEvent)} and {@link
     * SelectionStep#init(speedith.ui.selection.SelectionSequence, int)}. The
     * user interface will acceptSelection this function before the first click
     * event in this step and after every click event (i.e. after every call to
     * the {@link SelectionStep#acceptSelection(speedith.ui.SpiderDiagramClickEvent)}
     * function).</p>
     *
     * @param selection a list of selection steps and their accepted clicks.
     * @param thisIndex the index of this step within the selection sequence.
     * @return a value that indicates whether this selection step is finished.
     */
    public abstract boolean isFinished(SelectionSequence selection, int thisIndex);

    /**
     * Returns a value that indicates whether this step can be skipped. <p>This
     * value can change only after the calls to {@link
     * SelectionStep#acceptSelection(speedith.ui.SpiderDiagramClickEvent)} and {@link
     * SelectionStep#init(speedith.ui.selection.SelectionSequence, int)}. The
     * user interface will acceptSelection this function before the first click
     * event in this step and after every click event (i.e. after every call to
     * the {@link SelectionStep#acceptSelection(speedith.ui.SpiderDiagramClickEvent)}
     * function).</p>
     *
     * @param selection a list of selection steps and their accepted clicks.
     * @param thisIndex the index of this step within the selection sequence.
     * @return a value that indicates whether this step can be skipped.
     */
    public abstract boolean isSkippable(SelectionSequence selection, int thisIndex);

    /**
     * Returns an internationalised instructional message for the user. This
     * message contains human-readable instructions on what elements to select
     * and how.
     *
     * @param selection a list of selection steps and their accepted clicks.
     * @param thisIndex the index of this step within the selection sequence.
     * @return an internationalised instructional message for the user.
     */
    public String getInstruction(SelectionSequence selection, int thisIndex) {
        return this.getInstruction(Locale.getDefault(), selection, thisIndex);
    }

    /**
     * Returns an internationalised instructional message for the user. This
     * message contains human-readable instructions on what elements to select
     * and how.
     *
     * @param locale the locale in which to return the internationalised
     * message.
     * @param selection a list of selection steps and their accepted clicks.
     * @param thisIndex the index of this step within the selection sequence.
     * @return an internationalised instructional message for the user.
     */
    public abstract String getInstruction(Locale locale, SelectionSequence selection, int thisIndex);

    /**
     * This method is invoked by the {@link ElementSelectionDialog element
     * selection dialog} whenever the user clicks on the diagram. <p>If this
     * method returns {@code null} then the click is accepted and is added to
     * the list of accepted click events of this step in the given {@link SelectionSequence
     * selection sequence}. If any non-{@code null} value is returned, the click
     * is rejected and a message is displayed to the user.</p>
     *
     * @param selection the object that carries information on what has been
     * selected in this step.
     * @param selectionSeq a list of selection steps and their accepted clicks.
     * @param thisIndex the index of this step within the selection sequence.
     * @return {@code null} if the click should be accepted, and a non-{@code null}
     * value if the click should be rejected. In the latter case the returned
     * object should also contain a message explaining the reason for rejection.
     */
    public abstract SelectionRejectionExplanation acceptSelection(RuleArg selection, SelectionSequence selectionSeq, int thisIndex);

    /**
     * This method indicates whether the selection sequence UI should clean all
     * the selection of this step when the user presses the "previous" button.
     * In fact, this method indicates that all selection made for this step
     * should be cleaned whenever (just before) the {@link SelectionStep#init(speedith.core.reasoning.args.selection.SelectionSequence, int)
     * }
     * method is called.
     *
     * @return a value that indicates whether the selection sequence UI should
     * clean all the selection of this step when the user presses the "previous"
     * button.
     */
    public abstract boolean cleanSelectionOnStart();

    /**
     * Returns a value that indicates which elements of the diagram should be
     * selectable for this step. <p>This is a binary combination of: <ul> <li>{@link SelectionStep#Spiders},</li> <li>{@link SelectionStep#Zones},</li> <li>{@link SelectionStep#Contours},</li> <li>{@link SelectionStep#Operators},
     * and</li> <li>{@link SelectionStep#NullSpiderDiagrams}.</li> </ul></p>
     * <p>The value {@link SelectionStep#All} can be used to indicate that all
     * diagrammatic elements should be selectable.</p>
     *
     * @return a value that indicates which elements of the diagram should be
     * selectable for this step.
     */
    public abstract int getSelectableElements();
    // </editor-fold>
}
