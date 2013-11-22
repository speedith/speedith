/*
 *   Project: Speedith
 * 
 * File name: SpiderDiagramClickEvent.java
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
package speedith.ui;

import java.util.EventObject;
import static speedith.core.i18n.Translations.i18n;
import speedith.core.lang.SpiderDiagram;
import speedith.core.reasoning.args.*;
import speedith.icircles.util.ICirclesToSpeedith;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class SpiderDiagramClickEvent extends EventObject {

    private final SpiderDiagram diagram;
    private final DiagramClickEvent detailedEvent;
    private final int subDiagramIndex;
    private RuleArg ruleArg = null;

    /**
     * Initialises detailed event information of a {@link SpiderDiagramClickListener#spiderDiagramClicked(speedith.ui.SpiderDiagramClickEvent)
     * spider diagram click event}.
     *
     * @param source the panel in which the mouse click event happened.
     * @param diagram the diagram that was clicked.
     * @param eventDetail contains the information on which element of the
     * diagram was clicked (spider, zone, contour, or none).
     * @param subDiagramIndex the index of the sub-diagram that was clicked.
     */
    public SpiderDiagramClickEvent(SpiderDiagramPanel source, SpiderDiagram diagram, DiagramClickEvent eventDetail, int subDiagramIndex) {
        super(source);
        if (source == null) {
            throw new IllegalArgumentException("The argument 'source' must not be null.");
        }
        if (diagram == null) {
            throw new IllegalArgumentException("The argument 'diagram' must not be null.");
        }
        if (subDiagramIndex < 0 || subDiagramIndex >= diagram.getSubDiagramCount()) {
            throw new IllegalArgumentException(i18n("GERR_INDEX_OUT_OF_RANGE", "subDiagramIndex", "0", "diagram.getSubDiagramCount()"));
        }
        this.diagram = diagram;
        this.detailedEvent = eventDetail;
        this.subDiagramIndex = subDiagramIndex;
    }

    @Override
    public SpiderDiagramPanel getSource() {
        return (SpiderDiagramPanel) super.getSource();
    }

    @Override
    public String toString() {
        return toString(new StringBuilder(), getDetailedEvent()).append(getDetailedEvent() == null ? "" : " ").append("Sub-diagram: ").append(getSubDiagramIndex()).toString();
    }

    /**
     * Returns the description of the given event.
     *
     * @param event the event of which description we want.
     * @return the description of the given event.
     */
    public static String toString(DiagramClickEvent event) {
        return toString(new StringBuilder(), event).toString();
    }

    /**
     * Puts a string description of the event into the string builder.
     *
     * @param sb the string builder into which to print the event description.
     * @param event the event of which the description will be appended to the
     * given string builder.
     * @return the given string builder (with the event description appended).
     */
    public static StringBuilder toString(StringBuilder sb, DiagramClickEvent event) {
        if (event instanceof SpiderClickedEvent) {
            ICirclesToSpeedith.convert(((SpiderClickedEvent) event).getZoneOfFoot()).toString(sb.append("Spider: ").append(((SpiderClickedEvent) event).getFoot().getSpider().as.getName()).append(". Zone: "));
        } else if (event instanceof ContourClickedEvent) {
            sb.append("Contour: ").append(((ContourClickedEvent) event).getContour().ac.getLabel());
        } else if (event instanceof ZoneClickedEvent) {
            ICirclesToSpeedith.convert(((ZoneClickedEvent) event).getZone()).toString(sb.append("Zone: "));
        } else if (event != null) {
            throw new IllegalStateException(speedith.core.i18n.Translations.i18n("GERR_ILLEGAL_STATE"));
        }
        sb.append(".");
        return sb;
    }

    /**
     * Returns the diagram that was clicked.
     *
     * @return the diagram that was clicked.
     */
    public SpiderDiagram getDiagram() {
        return diagram;
    }

    /**
     * Returns the index of the sub-diagram in which the click event occurred.
     * <p>To obtain a reference.</p>
     *
     * @return
     */
    public int getSubDiagramIndex() {
        return subDiagramIndex;
    }

    /**
     * Gives more information on what has been clicked in the {@link
     * SpiderDiagramClickEvent#getSource() source diagram}. <p>This method may
     * return {@code null} to tell that no particular element in a diagram has
     * been clicked, instead the diagram as a whole was clicked.</p> <p>This
     * method can return objects of one of the following types: <ul> <li>{@link SpiderClickedEvent spider click event},</li> <li>{@link ContourClickedEvent contour click event},
     * and</li> <li>{@link ZoneClickedEvent zone click event}.</li> </ul> </p>
     *
     * @return an object detailing what exactly has been clicked in the diagram.
     * This method may also return {@code null} to tell that no particular
     * element in a diagram has been clicked, instead the diagram as a whole was
     * clicked.
     */
    public DiagramClickEvent getDetailedEvent() {
        return detailedEvent;
    }

    /**
     * Extracts all selection information from this click event, produces the
     * most (straight-forwardly) suitable {@link RuleArg rule argument}, and
     * returns the result. <p><span style="font-weight:bold">Note</span>: the {@link SubgoalIndexArg#getSubgoalIndex() subgoal index}
     * of the returned rule argument will be -1.</p> <p>This argument is stored
     * when the rule argument is extracted for the first time and then the same
     * instance will be returned for subsequent calls to this method.</p>
     *
     * @return a rule argument corresponding to the clicked diagrammatic
     * element.
     */
    public RuleArg toRuleArg() {
        if (ruleArg == null) {
            if (getDetailedEvent() instanceof SpiderClickedEvent) {
                SpiderClickedEvent spiderClickedEvent = (SpiderClickedEvent) getDetailedEvent();
                ruleArg = new SpiderZoneArg(-1, getSubDiagramIndex(), spiderClickedEvent.getSpiderName(), ICirclesToSpeedith.convert(spiderClickedEvent.getZoneOfFoot()));
            } else if (getDetailedEvent() instanceof ContourClickedEvent) {
                ContourClickedEvent contourClickedEvent = (ContourClickedEvent) getDetailedEvent();
                ruleArg = new ContourArg(-1, getSubDiagramIndex(), contourClickedEvent.getContourLabel());
            } else if (getDetailedEvent() instanceof ZoneClickedEvent) {
                ZoneClickedEvent zoneClickedEvent = (ZoneClickedEvent) getDetailedEvent();
                ruleArg = new ZoneArg(-1, getSubDiagramIndex(), ICirclesToSpeedith.convert(zoneClickedEvent.getZone()));
            } else if (getDetailedEvent() != null) {
                throw new IllegalStateException(speedith.core.i18n.Translations.i18n("GERR_ILLEGAL_STATE"));
            } else {
                ruleArg = new SubDiagramIndexArg(-1, getSubDiagramIndex());
            }
        }
        return ruleArg;
    }
}
