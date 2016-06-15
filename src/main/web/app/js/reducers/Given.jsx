import { SAVE_GIVEN_INDEX } from '../actions'

const Given = (state=[], action) => {

  switch (action.type) {
    case SAVE_GIVEN_INDEX:
      return [...state, action.index]

    default:
      return state
  }
}

export default Given

