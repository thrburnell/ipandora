import { SAVE_ARBITRARY } from '../actions'

const SaveArbitrary = (state=[], action) => {

  switch (action.type) {
    case SAVE_ARBITRARY:
      return [...state, { name: action.name, domain: action.domain }]

    default:
      return state
  }
}

export default SaveArbitrary

