package ss.project;

public class Field {
    int x,y,z;
    //@invariant x,y,z >= 0;
    
    @Override
    public boolean equals(Object o) {
        if (o instanceof Field) {
            return this.hashCode() == ((Field)o).hashCode();
        }
        return false;
    }
    @Override
    public int hashCode() {
        return x*100+y*10+z;
    }
}
