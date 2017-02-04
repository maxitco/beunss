package ss.project.game;

public enum Mark {
    X, O;
	
    
    public Mark other() {
        if (this == X) {
            return O;
        }
        if (this == O) {
            return X;
        }
        return null;
    }
    
    public String toString() {
        if (this == X) {
            return new String("X");
        }
        if (this == O) {
            return new String("O");
        }
        return "";
    }
}
