package spiderdrawer.shape.containers;

public abstract class Container<T,S> {

	protected S parent;
	
	public Container(S parent) {
		this.parent = parent;
	}
	
}
