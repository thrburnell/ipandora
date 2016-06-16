import React from 'react'

const AddGiven = ({ 
  fields: { formula }, 
  onSubmit,
  error,
  resetForm,
  handleSubmit,
  submitting
}) => {

  let givenEntry

  const formClassName = ["form-horizontal",
    formula.touched && formula.error ? "has-error" : ""].join(" ")

  return (
    <form className={ formClassName } onSubmit={ handleSubmit }>
      <div className="form-group">
        <div className="col-sm-10">
          <input type="text" {...formula}
          className="form-control monospace-font" placeholder="\FORALL x. (dragon(x) ...)" />
        </div>
        <div className="col-sm-2 text-right">
          <button type="submit" className="btn btn-primary full-width"
           disabled={submitting}>Add</button>
        </div>
      </div>
    </form>
  )
}

export default AddGiven

