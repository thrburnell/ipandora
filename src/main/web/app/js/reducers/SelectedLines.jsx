import { SELECT_LINE, DESELECT_LINE, CLOSE_PROOF_STEP } from '../actions'

const SelectedLines = (state=[], action) => {

  switch (action.type) {
    case SELECT_LINE:
      return [...state, action.index]
    
    case DESELECT_LINE:
      return state.filter(id => id != action.index)
   
    case CLOSE_PROOF_STEP:
      return []

    default:
      return state
  }
}

export default SelectedLines

