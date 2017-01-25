package ss.project;

public class Field {
    public int x,y,z;
    //@invariant x,y,z >= 0;
    
    public Field(int newx, int newy, int newz) {
        this.x = newx;
        this.y = newy;
        this.z = newz;
    }
    
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
    
    public Field copy() {
        return new Field(this.x,this.y,this.z);
    }
}
