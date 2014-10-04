package spiderdrawer.shape;

import java.awt.Graphics2D;

import spiderdrawer.exception.EmptyContainerException;
import spiderdrawer.exception.InvalidShapeException;
import spiderdrawer.shape.containers.MultiContainer;
import spiderdrawer.shape.containers.SingleContainer;
import spiderdrawer.shape.interfaces.Drawable;
import spiderdrawer.shape.interfaces.Movable;

public class Spider implements Movable, Drawable {
	
	Label label;
	Point labelledPoint;
	SingleContainer<Box, Spider> box;
	boolean complete;
	MultiContainer<Line, Spider> lines;
	MultiContainer<Point, Spider> points;
	
	public Spider() {
		createContainers();
	}
	
	private void createContainers() {
		box = new SingleContainer<Box, Spider>(this);
		lines = new MultiContainer<Line, Spider>(this);
		points = new MultiContainer<Point, Spider>(this);
	}
	
	public void setLabel(char letter, int number) {
		if (isSinglePoint()) {
			setLabel(points.get(0), letter, number);
			labelledPoint = points.get(0);
		} else {
			if (lines.size() > 0) {
				Line line = lines.get(0);
				Point point;
				if (line.start.isFullyConnected()) {
					point = line.end;
				} else {
					point = line.start;
				}
				setLabel(point, letter, number);
				labelledPoint = point;
			}
		}
	}
	
	public void removeLabel() {
		if (labelledPoint != null)
			removeLabel(labelledPoint);
	
	}
	
	public String asString() throws EmptyContainerException, InvalidShapeException {
		if (!isValid())
			throw new InvalidShapeException("Spider");
		String result = "(\"" + label.letter + label.number + "\",[";
		if (isSinglePoint()) {
			result += points.get(0).asString();
		} else {
			for (int i = 0; i < lines.size(); i++) {
				result += lines.get(i).asString();
				if (i != lines.size() -1)
					result += ",";
			}
		}
		return result + "])";
	}
	
	private void setLabel(Point point, char letter, int number) {
		label = new Label(letter, number, point.x - 15, point.y - 25);
		point.label = label;
	}
	
	private void removeLabel(Point point) {
		point.label = null;
		label = null;
		labelledPoint = null;
	}
	
	protected boolean isSinglePoint() {
		return (points.size() == 1 && lines.size() == 0);
	}
	
	@Override
	public boolean isValid() {
		if (label == null)
			return false;
		
		if (isSinglePoint()) {
			return points.get(0).isValid();
		} else {
			for (int i = 0; i < lines.size(); i++) {
				if (!lines.get(i).isValid())
					return false;
			}		
		}
		return true;
	}

	@Override
	public void draw(Graphics2D g2) {
		if (label != null) {
			label.draw(g2);
		}
	}
	
	public boolean containsLine(Line line) {
		if (isSinglePoint())
			return false;
		for (int i = 0; i < lines.size(); i++) {
			if (lines.get(i).equals(line)) {
				return true;
			}
		}
		return false;
	}

	public boolean intersects(Line line) {
		if (isSinglePoint()) {
			return points.get(0).intersects(line);
		} else {
			for (int i = 0; i < lines.size(); i++) {
				if (lines.get(i).intersects(line)) {
					return true;
				}
			}
		}
		return false;
	}

	@Override
	public void recompute(boolean moving) {
		if (isSinglePoint()) {
			points.get(0).recompute(moving);
		} else {
			for (int i = 0; i < lines.size(); i++) {
				lines.get(i).recompute(moving);
			}
		}
	}
	
	protected void computeBox() {
		Box box = null;
		removeLabel();
		for (int i = 0; i < points.size(); i++) {
			if (points.get(i).boxes.size() != 1) {
				box = null;
				break;
			}
			if (i == 0)
				box = points.get(0).boxes.get(0);
			if (!box.equals(points.get(i).boxes.get(0))) {
				box = null;
				break;
			}
		}
		if (this.box.get() != box) {
			Box tempBox = this.box.get();
			this.box.set(box, (box != null)? box.spiders : null);
			if (tempBox != null)
				tempBox.computeSpiderLabels();
		}	
		if (complete && box != null && box.innerBoxes.size() == 0) {
			this.box.get().checkLetter();
			setLabel(this.box.get().letter, this.box.get().spiders.indexOf(this)+1);
		} else {
			Box tempBox = this.box.get();
			this.box.set(null, null);
			if (tempBox != null)
				tempBox.computeSpiderLabels();
		}
	}

	@Override
	public boolean isWithin(Point p) {
		if (isSinglePoint()) {
			return points.get(0).isWithin(p);
		} else {
			for (int i = 0; i < lines.size(); i++) {
				if (lines.get(i).isWithin(p)) {
					return true;
				}
			}
		}
		return false;
	}
	
	@Override
	public void move(Point from, Point to) {
		if (isSinglePoint()) {
			points.get(0).move(from, to);
		} else {
			Line previous = null;
			for (int i = 0; i < lines.size(); i++) {
				if (previous == null) {
					lines.get(i).move(from, to, true);
					previous = lines.get(i);
				} else {
					if (lines.get(i).start.whichLine(previous) == 0) {
						lines.get(i).start.move(from, to);
					} else {
						lines.get(i).end.move(from, to);
					}
					previous = lines.get(i);
				}
			}
		}
	}

	@Override
	public double boundaryDistance(Point p) {
		if (isSinglePoint()) {
			return points.get(0).boundaryDistance(p);
		} else {
			double minDist = Double.MAX_VALUE;
			for (int i = 0; i < lines.size(); i++) {
				double dist = lines.get(i).boundaryDistance(p);
				if (dist < minDist)
					minDist = dist;
			}
			return minDist;
		}
	}
	
	protected void add(Spider spider) {
		while (spider.lines.size() > 0) {
			Line line = spider.lines.get(0);
			this.lines.add(line, line.spider);
		}
		while (spider.points.size() > 0) {
			Point point = spider.points.get(0);
			this.points.add(point, point.spider);
		}
		setComplete();
		computeBox();
	}
	
	protected void add(Point point) {
		points.add(point, point.spider);
		setComplete();
		computeBox();
	}
	
	protected void add(Line line) {
		lines.add(line, line.spider);
		setComplete();
		computeBox();
	}
	
	public void setComplete() {
		if (!isSinglePoint()) {
			for (int i = 0; i < lines.size(); i++) {
				if (!lines.get(i).hasBothEnds() /*&& points.contains(lines.get(i).start) && points.contains(lines.get(i).end)*/) {
					complete = false;
					return;
				}
			}
		}
		complete = true;
		return;
	}
	
	public void remove(Point point) {
		points.remove(point);
		Line line1, line2;
		if (point.line2 != null && point.line1 == null) {
			line1 = point.line2;
			line2 = point.line1;
		} else {
			line1 = point.line1;
			line2 = point.line2;
		}
		if (line2 != null) {
			Spider spider = new Spider();
			if (box.get() != null)
				spider.box.set(box.get(), box.get().spiders);
			Line iterLine = line2;
			Point iterPoint = point;
			do {
				spider.lines.add(iterLine, iterLine.spider);
				lines.remove(iterLine);
				if (!iterLine.hasBothEnds())
					break;
				iterPoint = iterLine.otherEnd(iterPoint);
				spider.points.add(iterPoint, iterPoint.spider);
				points.remove(iterPoint);
				iterLine = iterPoint.otherLine(iterLine);
			} while (iterLine != null);	
			spider.setComplete();
		}
		if (line1 == null) {
			remove();
		}
		complete = false;
		computeBox();
	}
	
	public void remove(Line line) {
		lines.remove(line);
		Point start, end;
		if (line.endSet && !line.startSet) {
			start = line.end;
			end = null;
		} else {
			if (labelledPoint == null || line.isConnected(labelledPoint, true)) {
				start = (line.startSet)? line.start : null;
				end = (line.endSet)? line.end : null;
			} else {
				start = (line.endSet)? line.end : null;
				end = (line.startSet)? line.start : null;
			}
		}
		if (end != null) {
			Spider spider = new Spider();
			if (box.get() != null)
				spider.box.set(box.get(), box.get().spiders);
			Line iterLine =	 line;
			Point iterPoint = end;
			spider.points.add(iterPoint, iterPoint.spider);
			points.remove(iterPoint);
			while (iterPoint.otherLine(iterLine) != null) {
				iterLine = iterPoint.otherLine(iterLine);
				spider.lines.add(iterLine, iterLine.spider);
				lines.remove(iterLine);
				if (!iterLine.hasBothEnds())
					break;
				iterPoint = iterLine.otherEnd(iterPoint);
				spider.points.add(iterPoint, iterPoint.spider);
				points.remove(iterPoint);
			}
			if (spider.box.get() != null) {
				spider.box.get().computeSpiderLabels();
			}
			spider.setComplete();
		}
		if (start == null) {
			remove();
		}
		setComplete();
		computeBox();
	}
	
	protected void remove() {
		removeLabel();
		Box tempBox = box.get();
		box.set(null, null);
		if (tempBox != null)
			tempBox.computeSpiderLabels();
	}
}
