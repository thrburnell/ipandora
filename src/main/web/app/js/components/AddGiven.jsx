import React from 'react'
import { connect } from 'react-redux'
import { addGiven } from '../actions'

let AddGiven = ({ dispatch }) => {

  let input

  return (
    <div>
      <input ref={node => {
        input = node
      }} />
      <button onClick={() => {
        dispatch(addGiven(input.value))
        input.value=''
      }}>
        Add Given
      </button>
    </div>
  )
}

AddGiven = connect()(AddGiven)

export default AddGiven

