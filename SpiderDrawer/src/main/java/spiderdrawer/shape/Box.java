package spiderdrawer.shape;

import java.awt.Color;
import java.awt.Graphics2D;
import java.awt.Rectangle;
import java.awt.geom.Area;
import java.awt.geom.Ellipse2D;
import java.util.ArrayList;

import spiderdrawer.exception.EmptyContainerException;
import spiderdrawer.exception.InvalidShapeException;
import spiderdrawer.shape.containers.MultiContainer;
import spiderdrawer.shape.containers.SingleContainer;
import spiderdrawer.shape.interfaces.Deletable;
import spiderdrawer.shape.interfaces.Drawable;
import spiderdrawer.shape.interfaces.Movable;
import spiderdrawer.shape.interfaces.Shape;
import static spiderdrawer.Parameters.*;

public class Box implements Drawable, Movable, Deletable {

	Point topLeft;
	int width;
	int height;
	char letter = '\0';
	private ArrayList<Shape> shapeList;
	MultiContainer<Circle, Box> circles;
	MultiContainer<Circle, Box> overlapCircles;
	MultiContainer<Circle, Box> outerCircles;
	MultiContainer<Line, Box> lines;
	MultiContainer<Line, Box> overlapLines;
	SingleContainer<Connective, Box> connective;
	boolean leftConnective;
	MultiContainer<Connective, Box> innerConnectives;
	MultiContainer<Box, Box> innerBoxes;
	SingleContainer<Box, Box> outerBox;
	MultiContainer<Box, Box> overlapBoxes;
	MultiContainer<Label, Box> labels;
	MultiContainer<Point, Box> points;
	ArrayList<Shape> toMove;
	MultiContainer<Spider, Box> spiders;
	SingleContainer<Shading, Box> shading;


	public Box(Point topLeft, int width, int height) {
		this.topLeft = topLeft;
		this.width = width;
		this.height = height;
	}
	
	public Box(int topLeftX, int topLeftY, int width, int height) {
		this(new Point(topLeftX, topLeftY), width, height);
	}
	
	private void createContainers() {
		circles = new MultiContainer<Circle, Box>(this);
		overlapCircles = new MultiContainer<Circle, Box>(this);
		outerCircles = new MultiContainer<Circle, Box>(this);
		lines = new MultiContainer<Line, Box>(this);
		overlapLines = new MultiContainer<Line, Box>(this);
		connective = new SingleContainer<Connective, Box>(this);
		innerConnectives = new MultiContainer<Connective, Box>(this);
		innerBoxes = new MultiContainer<Box, Box>(this);
		outerBox = new SingleContainer<Box, Box>(this);
		overlapBoxes = new MultiContainer<Box, Box>(this);
		labels = new MultiContainer<Label, Box>(this);
		points = new MultiContainer<Point, Box>(this);
		spiders = new MultiContainer<Spider, Box>(this);
		shading = new SingleContainer<Shading, Box>(this);
	}
	
	public static Box create(int topLeftX, int topLeftY, int width, int height, ArrayList<Shape> shapeList) {
		Box box = new Box(topLeftX, topLeftY, width, height);
		box.createContainers();
		box.shapeList = shapeList;
		box.recompute(false);
		box.computeShading();
		return box;
	}
	
	public static Box create(Freeform freeform, ArrayList<Shape> shapeList) {
		int minX = freeform.minX();
		int minY = freeform.minY();
		return create(minX, minY, freeform.maxX() - minX, freeform.maxY() - minY, shapeList);
	}
	
	public void resize(int width, int height) {
		this.width = width;
		this.height = height;
	}
	
	protected Point getTopLeft() {
		return topLeft;
	}
	
	protected int getWidth() {
		return width;
	}
	
	protected int getHeight() {
		return height;
	}
	
	public Connective getConnective() {
		return connective.get();
	}
	
	/*protected String asString() {
		return topLeft.x + "," + topLeft.y + "," + width + "," + height;
	}*/
	
	protected double distance(Point p) {
		if (intersects(p))
			return 0;
		return boundaryDistance(p);
	}
	
	private int size() {
		return width*height;
	}
	
	public boolean intersects(Point p) {
		return (topLeft.x <= p.x && p.x <= topLeft.x + width) && (topLeft.y <= p.y && p.y <= topLeft.y + height);
	}
	
	public double boundaryDistance(Point p) {
		Point topRight = topRight();
		Point bottomLeft = bottomLeft();
		Point bottomRight = bottomRight();
		Line top = new Line(topLeft, topRight);
		Line bottom = new Line(bottomLeft, bottomRight);
		Line left = new Line(topLeft, bottomLeft);
		Line right = new Line(topRight, bottomRight);
		return Math.min(Math.min(top.distance(p), bottom.distance(p)), Math.min(left.distance(p), right.distance(p)));
	}
	
	public boolean isOverlapping() {
		return !overlapCircles.isEmpty()  || !overlapLines.isEmpty() || !overlapBoxes.isEmpty(); 
	}
	
	public boolean containsSpider() {
		return !lines.isEmpty() || !circles.isEmpty();
	}
	
	public boolean completeConnectives() {
		if (innerConnectives.size() == 0)
			return innerBoxes.isEmpty();
		int numBoxes = 0;
		for (int i = 0; i < innerConnectives.size(); i++) {
			if (innerConnectives.get(i).isFullyConnected()) {
				if (innerConnectives.get(i).logical == Logical.NEGATION)
					numBoxes += 1;
				else
					numBoxes += 2;
			}
		}
		
		return !innerBoxes.isEmpty() && numBoxes == innerBoxes.size();
	}
	
	public boolean singleInnerConnective() {
		return innerConnectives.size() == 1;
	}
	
	public Connective getInnerConnective() {
		return innerConnectives.get(0);
	}
	
	public String spidersAsString() {
		String result = "[";
		if (spiders != null) {
			for (int i = 0; i < spiders.size(); i++) {
				result += "\"" + letter + (i+1) + "\"";	
				if (i != spiders.size()-1)
					result += ",";
			}
		}
		return result += "]";
	}
	
	public String habitatsAsString() throws EmptyContainerException, InvalidShapeException {
		String result = "[";
		if (spiders != null) {
			for (int i = 0; i < spiders.size(); i++) {
				result += spiders.get(i).asString();	
				if (i != spiders.size()-1)
					result += ",";
			}
		}
		return result += "]";
	}
	
	public String shadedZones(boolean empty) throws EmptyContainerException {
		String result = "";
		ArrayList<Shading> seenShadings = new ArrayList<Shading>();
		for (int i = 0; i < circles.size(); i++) {
			Circle circle = circles.get(i);
			for (int j = 0; j < circle.shadings.size(); j++) {
				if (!seenShadings.contains(circle.shadings.get(j)) && (!empty || !circle.shadings.get(j).containsSpider()) && doesOverlap(circle.shadings.get(j).included.list())) {
					result += circle.shadings.get(j).asString() + ",";
					seenShadings.add(circle.shadings.get(j));
				}
			}
			if (shading.get() != null) {
				result += shading.get().asString() + ",";
			}
		}
		if (result.length() > 1) {
			result = result.substring(0, result.length()-1);
		}
		return result;
	}
	
	public String visibleEmptyZones() throws EmptyContainerException {
		StringBuilder result = new StringBuilder(shadedZones(true));
		if (result.length() == 0 && circles.size() > 0) {
			ArrayList<Circle> temp = new ArrayList<Circle>();
			temp.add(circles.get(0));
			if (!checkZone(true, temp)) {
				addZones(result, temp);
				result.delete(result.length()-2, result.length());
			}
		}
		return "[" + result + "]";
	}
	
	public String shadedZones() throws EmptyContainerException {
		return "[" + shadedZones(false) + "]";
	}
	
	public String shadedAndMissingZones() throws EmptyContainerException {
		String result = "[";
		result += shadedZones(false);
		String missing = missingZones();
		if (result.length() > 1 && missing.length() > 0)
			result += ",";
		return result + missing + "]";
	}	
	
	public String missingZones() throws EmptyContainerException {
		StringBuilder result = new StringBuilder();
		checkZones(true, result, new ArrayList<Circle>(), 0);
		if (result.length() > 1)
			result.delete(result.length()-2, result.length());
		return result.toString();
	}
	
	public String presentZones() throws EmptyContainerException {
		StringBuilder result = new StringBuilder();
		checkZones(false, result, new ArrayList<Circle>(), 0);
		if (result.length() > 1)
			result.delete(result.length()-2, result.length());
		return "[" + result.toString() +  "]";
	}
	
	public void addZones(StringBuilder result, ArrayList<Circle> included) throws EmptyContainerException {
		@SuppressWarnings("unchecked")
		ArrayList<Circle> excluded = (ArrayList<Circle>) circles.list().clone();
		excluded.removeAll(included);
		StringBuilder temp = new StringBuilder();
		
		temp.append("([");
		printList(temp, included);
		temp.append("],[");
		printList(temp, excluded);
		temp.append("]), ");
		System.out.println(temp);
		result.append(temp);
	}
	
	public void printList(StringBuilder result, ArrayList<Circle> list) throws EmptyContainerException {
		for (int i = 0; i < list.size(); i++) {
			result.append("\"" + list.get(i).label.getWExc("Label").letter + "\"");
			if (i < list.size()-1)
				result.append(",");
		}
	}
	
	public void checkZones(boolean missing, StringBuilder result, ArrayList<Circle> found, int done) throws EmptyContainerException {
		for (int i = done; i < circles.size(); i++) {
			found.add(circles.get(i));
			checkZones(missing, result, found, i+1);
			found.remove(circles.get(i));
		}
		if (checkZone(missing, found))
			addZones(result, found);
	}	
	
	public boolean checkZone(boolean missing, ArrayList<Circle> included) {
		if (included.size() == 0)
			return false;
		Box box = included.get(0).boxes.get(0);
		Area area = new Area(new Rectangle(box.topLeft.x, box.topLeft.y, box.width, box.height));
		for (int i = 0; i < included.size(); i++) {
			Circle circle = included.get(i);
			area.intersect(new Area(new Ellipse2D.Float(circle.center.x-circle.radius, circle.center.y-circle.radius, circle.radius*2, circle.radius*2)));
		}
		@SuppressWarnings("unchecked")
		ArrayList<Circle> excluded = (ArrayList<Circle>) box.circles.list().clone();
		excluded.removeAll(included);
		if (excluded != null) {
			for (int i = 0; i < excluded.size(); i++) {
				Circle circle = excluded.get(i);
				area.subtract(new Area(new Ellipse2D.Float(circle.center.x-circle.radius, circle.center.y-circle.radius, circle.radius*2, circle.radius*2)));
			}
		}
		if (missing)
			return area.isEmpty();
		else
			return !area.isEmpty();
	}
	
	public boolean doesOverlap(ArrayList<Circle> list) {
		for (int i = 0; i < list.size()-1; i++) {
			Circle current = list.get(i);
			for (int j = i + 1; j < list.size(); j++) {
				if (!current.overlapCircles.contains(list.get(j)))
					return false;
			}
		}
		return true;
	}
	
	public String asString(boolean originalRep) throws EmptyContainerException, InvalidShapeException {
	    	if (isValid()) {
	    		if (singleInnerConnective()) {
	    			Connective connective = getInnerConnective();
	    			String args;
	    			if (connective.asString() == "not") {
	    				args = "arg1 = " + connective.getRightBox().asString(originalRep) + " "; 
	    			} else {
	    				args = "arg1 = " + connective.getLeftBox().asString(originalRep) + ", arg2 = " + connective.getRightBox().asString(originalRep) + " ";
	    			}
	    			return "BinarySD { "
	    					+ "operator= \"op " + connective.asString() + "\", "
	    					+ args
	    					+ "}";
	    		} else {
	    			return "PrimarySD { "
	    					+ "spiders = " + spidersAsString() + ", "
	    					+ "habitats = " +  habitatsAsString() + ", "
	    					+ "sh_zones = " +  (originalRep? shadedZones() : shadedAndMissingZones()) + ", "
	    					+ "present_zones = " + (originalRep? presentZones() : visibleEmptyZones()) + " "
	    					+ "}";
	    		}
	    	} else {
	    		throw new InvalidShapeException("Box");
	    	}
	}
	
	@Override
	public boolean isValid() {
		return completeConnectives() && !isOverlapping() && !(containsSpider() && !innerBoxes.isEmpty()) && outerCircles.isEmpty() && (singleInnerConnective() || innerConnectives.isEmpty());
	}
	
	@Override
	public void draw(Graphics2D g2) {
		if (!isValid()) {
			g2.setColor(Color.RED);
		} else {
			g2.setColor(Color.BLACK);
		}
		g2.drawRect(topLeft.getX(), topLeft.getY(), width, height);
		g2.setColor(Color.BLACK);
	}
	
	public void move(Point from, Point to, boolean external) {
		if (external) {
			topLeft.move(from, to);
			//if ((overlapCircles == null || overlapCircles.size() == 0) && (overlapBoxes == null || overlapBoxes.size() == 0) && (overlapLines == null || overlapLines.size() == 0)) {
				if (innerBoxes == null || innerBoxes.size() == 0) {
					for (int i = 0; i < circles.size(); i++) {
						circles.get(i).move(from, to, true);
					}
					for (int i = 0; i < circles.size(); i++) {
						circles.get(i).recompute(false);
					}
					for (int i = 0; i < spiders.size(); i++) {
						spiders.get(i).move(from, to);
					}
					for (int i = 0; i < spiders.size(); i++) {
						spiders.get(i).recompute(false);
					}
				}
				if (circles == null || circles.size() == 0) {
					if (singleInnerConnective() && innerConnectives.get(0).isFullyConnected()) {
						innerConnectives.get(0).move(from, to, true);
					}
				}
			//}
			if (connective.get() != null) {
				if ((leftConnective && this.leftDistance(connective.get()) > CONNECTIVE_BOX_DIST) || (!leftConnective && this.rightDistance(connective.get()) > CONNECTIVE_BOX_DIST)) {
					Connective oldCon = connective.get();
					connective.set(null, null);
					if (oldCon != null)
						oldCon.computeBoxes(Arrays.boxArray(shapeList));
				}
			}
		} else {
			move(from, to);
		}
	}

	@Override
	public void move(Point from, Point to) {
		Point topRight = topRight();
		Point bottomLeft = bottomLeft();
		Point bottomRight = bottomRight();
		Line top = new Line(topLeft, topRight);
		Line left = new Line(topLeft, bottomLeft);
		Line right = new Line(topRight, bottomRight);
		Line bottom = new Line(bottomLeft, bottomRight);
		double distTop = top.distanceAlongLine(from);
		double distLeft = left.distanceAlongLine(from);
		double distRight = right.distanceAlongLine(from);
		double distBottom = bottom.distanceAlongLine(from);
		double distTopAllowed = Math.min(DIST_LINE_MOVE_END,DIST_LINE_MOVE_END_MIN/top.length());
		double distRightAllowed = Math.min(DIST_LINE_MOVE_END,DIST_LINE_MOVE_END_MIN/right.length());
		double distLeftAllowed = Math.min(DIST_LINE_MOVE_END,DIST_LINE_MOVE_END_MIN/left.length());
		double distBottomAllowed = Math.min(DIST_LINE_MOVE_END,DIST_LINE_MOVE_END_MIN/bottom.length());
		if (distRight > 1-distRightAllowed && distBottom > 1-distBottomAllowed) { //Bottom right corner
			width += to.x - from.x;
			height += to.y - from.y;
		} else if (distLeft > 1-distLeftAllowed && distBottom < distBottomAllowed) { //Bottom left corner
			topLeft.x += to.x - from.x;
			width -= to.x - from.x;
			height += to.y - from.y;
		} else if (distLeft < distLeftAllowed && distTop < distTopAllowed) { //Top left corner
			topLeft.x += to.x - from.x;
			width -= to.x - from.x;
			topLeft.y += to.y - from.y;
			height -= to.y - from.y;
		} else if (distRight < distRightAllowed && distTop > 1-distTopAllowed) { //Top right corner
			width += to.x - from.x;
			topLeft.y += to.y - from.y;
			height -= to.y - from.y;
		} else {
			move(from, to, true);
		}
	}
		
	private void computeInnerBoxes(Box[] boxes) {
		innerBoxes.removeAll();
		for (int i = 0; i < boxes.length; i++) {
			if (this.contains(boxes[i]) && (boxes[i].outerBox.get() == null || boxes[i].outerBox.get().size() > size())) {
				innerBoxes.add(boxes[i], boxes[i].outerBox);
			}
		}
		
	}
	
	private void computeOuterBox(Box[] boxes) {
		int smallestBox = -1;
		int minBoxSize = Integer.MAX_VALUE;
		ArrayList<Box> outerBoxes = new ArrayList<Box>();
		for (int i = 0; i < boxes.length; i++) {
			if (boxes[i].contains(this) && boxes[i].overlapBoxes.size() == 0) {
				outerBoxes.add(boxes[i]);
				if (boxes[i].size() < minBoxSize) {
					smallestBox = outerBoxes.size()-1;
					minBoxSize = boxes[i].size();
				}
			}
		}
		
		if (smallestBox != -1)
			outerBox.set(outerBoxes.get(smallestBox), outerBoxes.get(smallestBox).innerBoxes);
	}
	
	public Box[] getInnerBoxes() {
		return innerBoxes.list().toArray(new Box[0]);
	}
	
	private void computeOverlapBoxes(Box[] boxes) {
		overlapBoxes.removeAll();
		for (int i = 0; i < boxes.length; i++) {
			if (this.intersects(boxes[i])) {
				overlapBoxes.add(boxes[i], boxes[i].overlapBoxes);
			}
		}
	}
	
	private void computeCircles(Circle[] circles) {
		outerCircles.removeAll();
		for (int i = 0; i < circles.length; i++) {
			if (circles[i].contains(this)) {
				outerCircles.add(circles[i], circles[i].innerBoxes);
			}
		}
		
		this.circles.removeAll();
		for (int i = 0; i < circles.length; i++) {
			if (this.contains(circles[i]) && !this.innerBoxesContains(circles[i])) {
				this.circles.add(circles[i], circles[i].boxes);
				if (outerBox.get() != null)
					outerBox.get().circles.remove(circles[i]);
			}
		}
	}
	
	/*private void removeOuterBoxes(Circle circle) {
		for (int i = 0; i < outerBoxes.size(); i++) {
			outerBoxes.get(i).circles.remove(circle);
		}
	}*/
	
	private void computeOverlapCircles(Circle[] circles) {
		overlapCircles.removeAll();
		for (int i = 0; i < circles.length; i++) {
			if (this.intersects(circles[i])) {
				overlapCircles.add(circles[i], circles[i].overlapBoxes);
			}
		}
	}
	
	private void computeLines(Line[] lines) {
		this.lines.removeAll();
		if (!innerBoxes.isEmpty()) {
			return;
		}
		for (int i = 0; i < lines.length; i++) {
			if (this.contains(lines[i])) {
				this.lines.add(lines[i], lines[i].boxes);
			}
		}
	}
	
	/*
	 * Relies on computeBoxes() (outerBox computed) being called beforehand.
	 */
	private void computePoints(Point[] points) {
		this.points.removeAll();
		if (!innerBoxes.isEmpty()) {
			return;
		}
		for (int i = 0; i < points.length; i++) {
			if (this.contains(points[i])) {
				points[i].boxes.remove(outerBox.get());
				this.points.add(points[i], points[i].boxes);
			}
		}
	}
	
	private void computeOverlapLines(Line[] lines) {
		overlapLines.removeAll();
		for (int i = 0; i < lines.length; i++) {
			if (this.intersects(lines[i])) {
				overlapLines.add(lines[i], lines[i].overlapBoxes);
			}
		}
	}
	

	
	private void computeConnectives() {
		if (outerBox.get() == null)
			return;
		Connective[] connectives = outerBox.get().innerConnectives.list().toArray(new Connective[0]);
		Box[] boxes = outerBox.get().getInnerBoxes();
		int connectivePos = -1;
		double lowestDist = Double.MAX_VALUE;
		boolean left = true;
		for (int i = 0; i < connectives.length; i++) {
			double leftDist = this.leftDistance(connectives[i]);
			double rightDist = this.rightDistance(connectives[i]);
			double minDist = Math.min(leftDist, rightDist);
			boolean done = false;
			for (int j = 0; j < boxes.length; j++) {
				if (minDist == leftDist) {
					if (this.leftDistance(boxes[j]) < minDist)
						done = true;
				} else {
					if (this.rightDistance(boxes[j]) < minDist)
						done = true;
				}			
			}
			if (done)
				continue;
			if (minDist < lowestDist) {
				if (connectives[i].logical != Logical.NEGATION || (minDist != rightDist)) { //Only allow left connective when not a negation.
					lowestDist = minDist;
					connectivePos = i;
					left = (minDist == leftDist);
				}
			}
		}
		if (connective.get() == null /*&& lowestDist <= CONNECTIVE_BOX_DIST*/ && connectivePos != -1) {
			
			double oldDist = Double.MAX_VALUE;
			if ((left? connectives[connectivePos].rightBox.get() : connectives[connectivePos].leftBox.get()) != null) {
					oldDist = left? connectives[connectivePos].rightBox.get().leftDistance(connectives[connectivePos]) : 
									connectives[connectivePos].leftBox.get().rightDistance(connectives[connectivePos]);
			}
			if (lowestDist < oldDist) {
				Box oldBox;
				if (left) {
					oldBox = connectives[connectivePos].rightBox.get();
					connective.set(connectives[connectivePos], connectives[connectivePos].rightBox);
				} else {
					oldBox = connectives[connectivePos].leftBox.get();
					connective.set(connectives[connectivePos], connectives[connectivePos].leftBox);
				}	
				leftConnective = left;
				if (oldBox != null && oldBox != this)
					oldBox.computeConnectives();
			}
		}
	}
	
	protected boolean innerBoxesContains(Connective connective) {
		if (innerBoxes != null) {
			for (int i = 0; i < innerBoxes.size(); i++) {
				if (innerBoxes.get(i).contains(connective)) {
					return true;
				}
			}
		}
		return false;
	}
	
	protected boolean innerBoxesContains(Box box) {
		if (innerBoxes != null) {
			for (int i = 0; i < innerBoxes.size(); i++) {
				if (innerBoxes.get(i).contains(box)) {
					return true;
				}
			}
		}
		return false;
	}
	
	
	protected boolean innerBoxesContains(Circle circle) {
		for (int i = 0; i < innerBoxes.size(); i++) {
			if (innerBoxes.get(i).contains(circle)) {
				return true;
			}
		}
		return false;
	}
	
	protected boolean innerBoxesContains(Freeform freeform) {
		for (int i = 0; i < innerBoxes.size(); i++) {
			if (innerBoxes.get(i).contains(freeform)) {
				return true;
			}
		}
		return false;
	}
	
	protected boolean innerBoxesContains(Label label) {
		for (int i = 0; i < innerBoxes.size(); i++) {
			if (innerBoxes.get(i).contains(label)) {
				return true;
			}
		}
		return false;
	}
	
	private void computeInnerConnectives(Connective[] connectives) {
		for (int i = 0; i < innerConnectives.size(); i++)
			innerConnectives.get(i).computeOuterBoxes(Arrays.boxArray(shapeList));
		innerConnectives.removeAll();
		for (int i = 0; i < connectives.length; i++) {
			if (this.contains(connectives[i]) && !innerBoxesContains(connectives[i])) {
				innerConnectives.add(connectives[i], connectives[i].outerBox);
			}
		}
	}
	
	private void computeLabels(Label[] labels) {
		this.labels.removeAll();
		for (int i = 0; i < labels.length; i++) {
			if (this.contains(labels[i]) && !innerBoxesContains(labels[i])) {
				this.labels.add(labels[i], labels[i].box);
			}
		}
	}
	
	private void computeShading() {
		if (shading.get() == null && outerBox.get() != null && outerBox.get().shading.get() != null) {
			shading.set(outerBox.get().shading.get(), outerBox.get().shading.get().box);
		}
	}
	
	@Override
	public void recompute(boolean moving) {
		if (shapeList == null)
			return;
		if (!moving) {
			computeInnerBoxes(Arrays.boxArray(shapeList));
			computeOuterBox(Arrays.boxArray(shapeList));
			computeCircles(Arrays.circleArray(shapeList));
			for (int i = 0; i < this.circles.size(); i++) {
				this.circles.get(i).computeLabels(Arrays.labelArray(shapeList));
			}
			computeLabels(Arrays.labelArray(shapeList));
			for (int i = 0; i < this.labels.size(); i++) {
				this.labels.get(i).computeLabels(Arrays.labelArray(shapeList));
			}
			computeLines(Arrays.lineArray(shapeList));
			computePoints(Arrays.pointArray(shapeList));
			computeInnerConnectives(Arrays.connectiveArray(shapeList));

		}
		computeConnectives();
		computeOverlapCircles(Arrays.circleArray(shapeList));
		computeOverlapLines(Arrays.lineArray(shapeList));
		computeOverlapBoxes(Arrays.boxArray(shapeList));
		computeSpiders();	
		if (outerBox.get() != null)
			for (int j = 0; j < outerBox.get().spiders.size(); j++) {
				int size = outerBox.get().spiders.size();
				outerBox.get().spiders.get(j).computeBox();
				if (outerBox.get().spiders.size() < size)
					j--;
			}
		computeSpiderLabels();
	}
	
	protected void checkLetter() {
		if (letter == '\0') {
			Box[] boxes = Arrays.boxArray(shapeList);
			ArrayList<Character> letters = new ArrayList<Character>(); 
			for (int i = 0; i < boxes.length; i++) {
				boxes[i].clearLetter();
				if (boxes[i].letter != '\0')
					letters.add(boxes[i].letter);
			}
			for (int i = 0; i < 26; i++) {
				char possibleChar = (char) ('S' + ((i < 8)? i : i - 26));
				if (!letters.contains(new Character(possibleChar))) {
					letter = possibleChar;
					break;
				}
			}
		}
	}
	
	protected void computeSpiderLabels() {
		if (spiders.size() > 0)
			checkLetter();
		for (int i = 0; i < spiders.size(); i++)
			spiders.get(i).setLabel(letter, spiders.indexOf(spiders.get(i))+1);
	}
	
	private void clearLetter() {
		if (spiders.size() == 0)
			letter = '\0';
	}
	
	private void addSpider(Spider spider) {
		spiders.add(spider, spider.box);
	}
	
	protected void computeSpiders() {
		if (lines != null) {
			for (int i = 0; i < lines.size(); i++) {
				if (!spiders.contains(lines.get(i).spider.get()) && lines.get(i).spider.get().complete)
					addSpider(lines.get(i).spider.get());
			}
		}
		if (points != null) {
			for (int i = 0; i < points.size(); i++) {
				if (points.get(i).line1 != null || points.get(i).line2 != null)
					continue;
				if (!spiders.contains(points.get(i).spider.get()) && points.get(i).spider.get().complete)
					addSpider(points.get(i).spider.get());
			}
		}
		if (spiders.size() == 0)
			letter = '\0';
	}
	
	protected boolean contains(Box box) {
		if (this.equals(box))
			return false;
		return (this.topLeft.x < box.topLeft.x && this.topLeft.x + this.width > box.topLeft.x + box.width && this.topLeft.y < box.topLeft.y && this.topLeft.y + this.height > box.topLeft.y + box.height);
	}
	
	protected boolean contains(Circle circle) {
		boolean withinXDir = (topLeft.x < circle.center.x - circle.radius) && (circle.center.x + circle.radius < topLeft.x + width);
		boolean withinYDir = (topLeft.y < circle.center.y - circle.radius) && (circle.center.y + circle.radius < topLeft.y + height);
		return withinXDir && withinYDir;
	}
	
	protected boolean contains(Point point) {
		boolean withinXDir = (topLeft.x < point.x) && (point.x < topLeft.x + width);
		boolean withinYDir = (topLeft.y < point.y) && (point.y < topLeft.y + height);
		return withinXDir && withinYDir;
	}
	
	protected boolean contains(Freeform freeform) {
		for (int i = 0; i < freeform.points.size(); i++) {
			if (!contains(freeform.points.get(i)))
				return false;
		}
		return true;
	}
	
	protected boolean contains(Line line) {
		return this.contains(line.start) && this.contains(line.end);
	}
	
	protected boolean contains(Connective connective) {
		Box connectiveBox = new Box(connective.center.x - connective.width/2, connective.center.y - connective.height/2,connective.width, connective.height);
		return this.contains(connectiveBox);
	}
	
	protected boolean contains(Label label) {
		Box box = new Box(label.center.x - label.width/2, label.center.y - label.height/2, label.width, label.height);
		return this.contains(box);
	}
	
	protected Point topRight() {
		return new Point(topLeft.x+width, topLeft.y);
	}
	
	protected Point bottomLeft() {
		return new Point(topLeft.x, topLeft.y+height);
	}
	
	protected Point bottomRight() {
		return new Point(topLeft.x+width, topLeft.y+height);
	}
	
	protected boolean intersects(Box box) {
		if (this.equals(box))
			return false;
		Point topRight = new Point(topLeft.x + width, topLeft.y);
		Point bottomLeft = new Point(topLeft.x, topLeft.y + height);
		Point bottomRight = new Point(topLeft.x + width, topLeft.y + height);
		Line top = new Line(topLeft, topRight);
		Line bottom = new Line(bottomLeft, bottomRight);
		Line left = new Line(topLeft, bottomLeft);
		Line right = new Line(topRight, bottomRight);
		return box.intersects(top) || box.intersects(bottom) || box.intersects(left) || box.intersects(right);
	}
	
	protected boolean intersects(Circle circle) {
		Point topRight = new Point(topLeft.x + width, topLeft.y);
		Point bottomLeft = new Point(topLeft.x, topLeft.y + height);
		Point bottomRight = new Point(topLeft.x + width, topLeft.y + height);
		Line top = new Line(topLeft, topRight);
		Line bottom = new Line(bottomLeft, bottomRight);
		Line left = new Line(topLeft, bottomLeft);
		Line right = new Line(topRight, bottomRight);
		return circle.intersects(top) || circle.intersects(bottom) || circle.intersects(left) || circle.intersects(right);
	}
	
	protected double distance(Connective connective) {
		Point topRight = new Point(topLeft.x + width, topLeft.y);
		Point bottomLeft = new Point(topLeft.x, topLeft.y + height);
		Point bottomRight = new Point(topLeft.x + width, topLeft.y + height);
		Line top = new Line(topLeft, topRight);
		Line bottom = new Line(bottomLeft, bottomRight);
		Line left = new Line(topLeft, bottomLeft);
		Line right = new Line(topRight, bottomRight);
		return Math.min(Math.min(top.distance(connective.center), bottom.distance(connective.center)), Math.min(left.distance(connective.center), right.distance(connective.center)));
	}
	
	protected double leftDistance(Connective connective) {
		Point bottomLeft = new Point(topLeft.x, topLeft.y + height);
		Line left = new Line(topLeft, bottomLeft);
		Point closest = connective.center.plus(new Point(connective.width/2,0));
		if (left.start.x >= closest.x && topLeft.y <= closest.y-connective.width/2 && bottomLeft.y >= closest.y+connective.width/2) { //connective is left of line.
			return left.distance(connective.center);
		}
		return Double.MAX_VALUE;
	}

	protected double rightDistance(Connective connective) {
		Point topRight = new Point(topLeft.x + width, topLeft.y);
		Point bottomRight = new Point(topLeft.x + width, topLeft.y + height);
		Line right = new Line(topRight, bottomRight);
		Point closest = connective.center.minus(new Point(connective.width/2,0));
		if (right.start.x <= closest.x && topLeft.y <= closest.y-connective.width/2 && bottomRight.y >= closest.y+connective.width/2 ) {//connective is right of line. 
			return right.distance(connective.center);
		}
		return Double.MAX_VALUE;
	}
	
	private double leftDistance(Box box) {
		int distance = box.topLeft.x - (topLeft.x + width);
		return distance > 0? distance : Double.MAX_VALUE;
	}
	
	private double rightDistance(Box box) {
		int distance = topLeft.x - (box.topLeft.x + box.width);
		return distance > 0? distance : Double.MAX_VALUE;
	}
	
	protected double leftDistance(Freeform freeform) {
    	int minY = freeform.minY();
    	int maxX = freeform.maxX();
    	int maxY = freeform.maxY();
    	Point bottomLeft = new Point(topLeft.x, topLeft.y + height);
		Line left = new Line(topLeft, bottomLeft);
		Point closest = new Point(maxX, (minY+maxY)/2);
		if (left.start.x >= closest.x) {//freeform is right of line. 
			return left.distance(closest);
		}
		return Double.MAX_VALUE;
	}
	
	protected double rightDistance(Freeform freeform) {
		int minX = freeform.minX();
    	int minY = freeform.minY();
    	int maxY = freeform.maxY();
		Point topRight = new Point(topLeft.x + width, topLeft.y);
		Point bottomRight = new Point(topLeft.x + width, topLeft.y + height);
		Line right = new Line(topRight, bottomRight);
		Point closest = new Point(minX, (minY+maxY)/2);
		if (right.start.x <= closest.x) {//freeform is right of line. 
			return right.distance(closest);
		}
		return Double.MAX_VALUE;
	}
	
	@Override
	public boolean isWithin(Point p) {
		return Math.abs(this.boundaryDistance(p)) < BOX_MIN_DIST;
	}

	@Override
	public boolean intersects(Line line) {
		Point topRight = new Point(topLeft.x + width, topLeft.y);
		Point bottomLeft = new Point(topLeft.x, topLeft.y + height);
		Point bottomRight = new Point(topLeft.x + width, topLeft.y + height);
		Line top = new Line(topLeft, topRight);
		Line bottom = new Line(bottomLeft, bottomRight);
		Line left = new Line(topLeft, bottomLeft);
		Line right = new Line(topRight, bottomRight);
		return (top.intersects(line) || bottom.intersects(line) || left.intersects(line) || right.intersects(line));
	}

	@Override
	public void remove() {
		circles.removeAll();
		overlapCircles.removeAll();
		outerCircles.removeAll();
		lines.removeAll();
		overlapLines.removeAll();
		connective.set(null, null);
		innerBoxes.removeAll();
		for (int i = labels.size()-1; i >= 0; i--)
			labels.get(i).recompute(false);
		labels.removeAll();
		points.removeAll();
		if (outerBox.get() != null)
			outerBox.get().recompute(false);
		outerBox.set(null, null);	
		for (int i = innerConnectives.size()-1; i >= 0; i--)
			innerConnectives.get(i).recompute(false);
		innerConnectives.removeAll();
		overlapBoxes.removeAll();
		
		for (int i = 0; i < spiders.size(); i++) {
			int size = spiders.size();
			spiders.get(i).recompute(false);
			if (spiders.size() < size) {
				i--;
			}
		}
		
		spiders.removeAll();
		shapeList.remove(shading.get());
		shading.set(null, null);
	}
}
