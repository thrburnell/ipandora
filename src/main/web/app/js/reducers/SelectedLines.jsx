import { SELECT_LINE, DESELECT_LINE } from '../actions'

const SelectedLines = (state=[], action) => {

  switch (action.type) {
    case SELECT_LINE:
      return [...state, action.index]
    
    case DESELECT_LINE:
      return state.filter(id => id != action.index)
    
    default:
      return state
  }
}

export default SelectedLines

