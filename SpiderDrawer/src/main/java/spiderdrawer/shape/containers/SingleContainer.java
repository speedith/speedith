package spiderdrawer.shape.containers;

import spiderdrawer.exception.EmptyContainerException;

public class SingleContainer<T,S> extends Container<T,S> {

	T t;
	Container<S,T> c;
	
	public SingleContainer(S parent) {
		super(parent);
	}
	
	public void set(T t, Container<S,T> c) {		
		T oldT = this.t;
		Container<S,T> oldC = this.c;
		this.t = t;
		this.c = c;
		if (oldT != null) {
			if (oldC instanceof SingleContainer) {
				((SingleContainer<S, T>) oldC).set(null, this);
				
			} else {
				((MultiContainer<S, T>) oldC).remove(parent);
			}
		}
		if (t != null) {
			if (c instanceof SingleContainer) {
				SingleContainer<S,T> singleContainer = (SingleContainer<S, T>) c;
				if (!parent.equals(singleContainer.get()))
					singleContainer.set(parent, this);
			} else {
				MultiContainer<S,T> multiContainer = (MultiContainer<S, T>) c;
				if (!multiContainer.contains(parent))
					multiContainer.add(parent, this);
			}
		}
			
	}
	
	public T get() {
		return t;
	}
	
	public T getWExc(String type) throws EmptyContainerException {
		if (t == null)
			throw new EmptyContainerException(parent.getClass().getSimpleName(), type);
		return t;
	}
}
